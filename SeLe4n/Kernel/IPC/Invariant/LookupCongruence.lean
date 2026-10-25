-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.Defs
import SeLe4n.Kernel.IPC.Invariant.NotificationQueue
import SeLe4n.Kernel.IPC.Operations.Endpoint
import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.IPC.CrossCore.EndpointCall

/-!
# WS-SM SM6.D — Pointwise-lookup congruence for the IPC invariant surface

Every conjunct of `ipcInvariantFull` reads the system state **only** through
`objects[·]?` lookups (`v0.36.136` retired the one that read the scheduler).  This module makes that observation a reusable theorem family:

* **§1** — per-conjunct transports `X_of_getElem_eq`: two states whose
  object lookups agree pointwise satisfy each conjunct interchangeably,
  assembled into `ipcInvariantFull_of_getElem_eq` (all nineteen
  conjuncts).  Pointwise (rather
  than structural `objects`-equality) matters because the cross-core wake
  (`enqueueRunnableOnCore`) re-inserts the woken TCB with an identical
  value: every lookup is unchanged while the Robin-Hood array
  representation may differ.  (The first eight members were landed with
  SM6.A inside the staged `CrossCore/EndpointCallInvariant.lean`; they
  live here — production — so the SM6.D whole-bundle closures for every
  cross-core transition share one family.)

* **§2** — `OffSchedulerAgrees`: the state relation the cross-core
  transitions actually induce against their single-core counterparts —
  object lookups agree pointwise and **every** non-`scheduler` field is
  equal (the wake's re-insert is the only object write that differs, and
  it is lookup-invisible; the scheduler substitution `wakeThread` /
  `removeRunnableOnCore` vs `ensureRunnable` / `removeRunnable` is
  unconstrained by the relation).

* **§3** — the scheduler-substitution agreements: `ensureRunnable`,
  `removeRunnable`, `removeRunnableOnCore`, and the already-`.ready`
  `wakeThread` each relate a state to its scheduler-substituted image.

* **§4** — step congruences: the store-level transition steps
  (`storeObject`, `storeTcbIpcStateAndMessage`, `consumeReply`,
  `consumeCallerReply`) map `OffSchedulerAgrees`-related inputs to
  `OffSchedulerAgrees`-related outputs with aligned control flow — the
  lever that lets a cross-core transition's post-state ride the
  single-core whole-bundle theorem even when stores execute *after* the
  object-visible wake.

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §0  Typed-getter congruences
-- ============================================================================

/-- Pointwise object-lookup agreement lifts to `getTcb?` agreement. -/
theorem getTcb?_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (tid : SeLe4n.ThreadId) : s2.getTcb? tid = s1.getTcb? tid := by
  unfold SystemState.getTcb?; rw [hEq]

/-- Pointwise object-lookup agreement lifts to `getReply?` agreement. -/
theorem getReply?_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (rid : SeLe4n.ReplyId) : s2.getReply? rid = s1.getReply? rid := by
  unfold SystemState.getReply?; rw [hEq]

/-- Pointwise object-lookup agreement lifts to `getSchedContext?` agreement. -/
theorem getSchedContext?_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (scId : SeLe4n.SchedContextId) : s2.getSchedContext? scId = s1.getSchedContext? scId := by
  unfold SystemState.getSchedContext?; rw [hEq]

/-- Pointwise object-lookup agreement lifts to `getNotification?` agreement. -/
theorem getNotification?_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (oid : SeLe4n.ObjId) : s2.getNotification? oid = s1.getNotification? oid := by
  unfold SystemState.getNotification?; rw [hEq]

/-- Pointwise object-lookup agreement lifts to `getEndpoint?` agreement. -/
theorem getEndpoint?_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (oid : SeLe4n.ObjId) : s2.getEndpoint? oid = s1.getEndpoint? oid := by
  unfold SystemState.getEndpoint?; rw [hEq]

/-- Pointwise object-lookup agreement lifts to `lookupTcb` agreement. -/
theorem lookupTcb_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (tid : SeLe4n.ThreadId) : lookupTcb s2 tid = lookupTcb s1 tid := by
  unfold lookupTcb SystemState.getTcb?; rw [hEq]

-- ============================================================================
-- §1  Frame lemmas for single TCB rewrites
-- ============================================================================

/-- **WS-LS LS2.3**: a TCB rewrite that keeps the thread's `ipcState` keeps
every queue head consistent — the shape of the syscall seam's register spill,
which rewrites the caller's register file before the dispatch runs. -/
theorem queueHeadBlockedConsistent_updateTcb_of_ipcState_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : TCB → TCB) (hInv : st.objects.invExt)
    (hF : ∀ t, (f t).ipcState = t.ipcState) (h : queueHeadBlockedConsistent st) :
    queueHeadBlockedConsistent (st.updateTcb tid f) := by
  intro epId ep hd tcb hEp hTcb
  have hEp' : st.objects[epId]? = some (.endpoint ep) := by
    by_cases hNe : tid.toObjId = epId
    · subst hNe
      cases hT : st.getTcb? tid with
      | none => rw [SystemState.updateTcb_eq_self_of_none hT] at hEp; exact hEp
      | some t =>
        have := SystemState.updateTcb_getTcb?_self st tid f hInv
        rw [hT, Option.map_some] at this
        rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp this] at hEp
        exact absurd hEp (by simp)
    · rw [SystemState.updateTcb_objects_ne st tid f epId hNe hInv] at hEp; exact hEp
  by_cases hNe : tid.toObjId = hd.toObjId
  · have hHd : hd = tid := ThreadId.toObjId_injective _ _ hNe.symm
    subst hHd
    cases hT : st.getTcb? hd with
    | none => rw [SystemState.updateTcb_eq_self_of_none hT] at hTcb; exact h epId ep hd tcb hEp' hTcb
    | some t =>
      have hSelf := SystemState.updateTcb_getTcb?_self st hd f hInv
      rw [hT, Option.map_some] at hSelf
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hSelf] at hTcb
      injection hTcb with hTcb
      injection hTcb with hTcb
      subst hTcb
      have hOrig := h epId ep hd t hEp' ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)
      rw [hF t]
      exact hOrig
  · rw [SystemState.updateTcb_objects_ne st tid f hd.toObjId hNe hInv] at hTcb
    exact h epId ep hd tcb hEp' hTcb

-- ============================================================================
-- §2  The off-scheduler agreement relation
-- ============================================================================

/-- WS-SM SM6.D: the state relation a cross-core transition induces against
its single-core counterpart — object lookups agree **pointwise** and every
non-`scheduler` field is **equal**; the `scheduler` field is unconstrained.
The cross-core substitutions (`wakeThread` / `removeRunnableOnCore` for
`ensureRunnable` / `removeRunnable`) differ from their single-core
counterparts only in scheduler placement plus the wake's lookup-invisible
identical-value TCB re-insert, so the two spines stay in this relation at
every step.

Field-wise (rather than a record-update encoding) so each step-congruence
proof discharges per field; if `SystemState` gains a field, this structure
must gain the matching clause — the §4 step congruences will fail to
elaborate otherwise, which is the intended tripwire. -/
structure OffSchedulerAgrees (s1 s2 : SystemState) : Prop where
  /-- WS-ZA ZA4.5: objects agree **off the run-queue links**, which are scheduler
      state that lives in the TCB. -/
  objects : s2.objectsAgreeOffRunLinks s1
  machine : s2.machine = s1.machine
  objectIndex : s2.objectIndex = s1.objectIndex
  objectIndexSet : s2.objectIndexSet = s1.objectIndexSet
  services : s2.services = s1.services
  irqHandlers : s2.irqHandlers = s1.irqHandlers
  lifecycle : s2.lifecycle = s1.lifecycle
  asidTable : s2.asidTable = s1.asidTable
  interfaceRegistry : s2.interfaceRegistry = s1.interfaceRegistry
  serviceRegistry : s2.serviceRegistry = s1.serviceRegistry
  cdt : s2.cdt = s1.cdt
  tlb : s2.tlb = s1.tlb
  perCoreTlb : s2.perCoreTlb = s1.perCoreTlb
  perCoreICache : s2.perCoreICache = s1.perCoreICache
  pendingIcacheMaintenance :
    s2.pendingIcacheMaintenance = s1.pendingIcacheMaintenance
  /-- WS-BP BP7.2: the physical-write ledger agrees. -/
  pendingPhysicalWrites :
    s2.pendingPhysicalWrites = s1.pendingPhysicalWrites
  /-- WS-SM SM8.C.8: the declassification audit trail agrees.  A scheduler-only
      substitution must not silently forge or drop a recorded downgrade. -/
  declassificationAuditLog :
    s2.declassificationAuditLog = s1.declassificationAuditLog
  /-- WS-SM SM9.A.1a: the declassification audit epoch agrees.  The trail's own
      clause says a scheduler-only substitution forges no downgrade; this one
      says it does not silently *renumber* the downgrades that are there —
      which, once drain exists, is a distinct way to falsify
      `declassificationAuditLog_timestamp_identifies_event`. -/
  declassificationAuditEpoch :
    s2.declassificationAuditEpoch = s1.declassificationAuditEpoch
  /-- WS-SM SM9.B.6: the declassification **refusal** ledger agrees.  The
      trail's clauses say a scheduler-only substitution neither forges nor
      renumbers an authorized downgrade; this one says it cannot forge, drop or
      re-order a recorded *attempt* — which, since the ledger's `version` is
      the token a monitor brackets its reads with, would also let a
      substitution hide an overwrite. -/
  declassificationRefusals :
    s2.declassificationRefusals = s1.declassificationRefusals
  /-- WS-SM SM9.D.5: the declassification **taint side table** agrees.

      The provenance analogue of the two clauses above, and load-bearing for the
      same reason: a scheduler substitution that silently re-keyed an object's
      taint would move a recorded downgrade's causal ancestry, so a chain the
      detector reports would name a different subject's history. -/
  declassificationTaint :
    s2.declassificationTaint = s1.declassificationTaint

namespace OffSchedulerAgrees

/-- Reflexivity. -/
theorem refl (st : SystemState) : OffSchedulerAgrees st st :=
  ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Symmetry. -/
theorem symm {s1 s2 : SystemState} (h : OffSchedulerAgrees s1 s2) :
    OffSchedulerAgrees s2 s1 :=
  ⟨h.objects.symm, h.machine.symm, h.objectIndex.symm,
   h.objectIndexSet.symm, h.services.symm, h.irqHandlers.symm, h.lifecycle.symm,
   h.asidTable.symm, h.interfaceRegistry.symm, h.serviceRegistry.symm, h.cdt.symm,
   h.tlb.symm, h.perCoreTlb.symm, h.perCoreICache.symm,
   h.pendingIcacheMaintenance.symm, h.pendingPhysicalWrites.symm, h.declassificationAuditLog.symm,
   h.declassificationAuditEpoch.symm, h.declassificationRefusals.symm,
   h.declassificationTaint.symm⟩

/-- Transitivity. -/
theorem trans {s1 s2 s3 : SystemState}
    (hFirst : OffSchedulerAgrees s1 s2) (hSecond : OffSchedulerAgrees s2 s3) :
    OffSchedulerAgrees s1 s3 :=
  ⟨hSecond.objects.trans hFirst.objects, hSecond.machine.trans hFirst.machine,
   hSecond.objectIndex.trans hFirst.objectIndex, hSecond.objectIndexSet.trans hFirst.objectIndexSet,
   hSecond.services.trans hFirst.services, hSecond.irqHandlers.trans hFirst.irqHandlers,
   hSecond.lifecycle.trans hFirst.lifecycle, hSecond.asidTable.trans hFirst.asidTable,
   hSecond.interfaceRegistry.trans hFirst.interfaceRegistry,
   hSecond.serviceRegistry.trans hFirst.serviceRegistry, hSecond.cdt.trans hFirst.cdt,
   hSecond.tlb.trans hFirst.tlb,
   hSecond.perCoreTlb.trans hFirst.perCoreTlb, hSecond.perCoreICache.trans hFirst.perCoreICache,
   hSecond.pendingIcacheMaintenance.trans hFirst.pendingIcacheMaintenance,
   hSecond.pendingPhysicalWrites.trans hFirst.pendingPhysicalWrites,
   hSecond.declassificationAuditLog.trans hFirst.declassificationAuditLog,
   hSecond.declassificationAuditEpoch.trans hFirst.declassificationAuditEpoch,
   hSecond.declassificationRefusals.trans hFirst.declassificationRefusals,
   hSecond.declassificationTaint.trans hFirst.declassificationTaint⟩

end OffSchedulerAgrees

-- ============================================================================
-- §3  Scheduler-substitution agreements
-- ============================================================================

/-- SM6.D: a scheduler-only record update agrees with its base state
off-scheduler. -/
theorem offSchedulerAgrees_scheduler_update (st : SystemState) (σ : SchedulerState) :
    OffSchedulerAgrees st { st with scheduler := σ } :=
  ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- WS-ZA ZA4.5: a step that writes only the object store and the scheduler,
and the store only off the run-queue links, agrees with its input
off-scheduler. -/
theorem OffSchedulerAgrees.of_runLinkStep {st st' : SystemState}
    (hD : st'.onlyObjectsSchedulerDiffer st) (hA : st'.objectsAgreeOffRunLinks st) :
    OffSchedulerAgrees st st' := by
  have hD' := hD
  unfold SystemState.onlyObjectsSchedulerDiffer at hD'
  refine ⟨hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [hD']; try rfl)

/-- SM6.D: `ensureRunnable` (the single-core boot enqueue) agrees with its
input off-scheduler — it writes the scheduler and the woken thread's run-queue
links. -/
theorem ensureRunnable_offSchedulerAgrees (st : SystemState) (tid : SeLe4n.ThreadId) :
    OffSchedulerAgrees st (ensureRunnable st tid) :=
  .of_runLinkStep (ensureRunnable_onlyObjectsSchedulerDiffer st tid)
    (ensureRunnable_objectsAgreeOffRunLinks st tid)

/-- SM6.D: `removeRunnable` (the single-core boot dequeue) agrees with its
input off-scheduler. -/
theorem removeRunnable_offSchedulerAgrees (st : SystemState) (tid : SeLe4n.ThreadId) :
    OffSchedulerAgrees st (removeRunnable st tid) :=
  .of_runLinkStep (removeRunnable_onlyObjectsSchedulerDiffer st tid)
    (removeRunnable_objectsAgreeOffRunLinks st tid)

/-- WS-ZA ZA4.6: joining a reply-waiter queue writes the object store alone,
off the run-queue (and reply-waiter) links. -/
theorem linkReplyWaiter_offSchedulerAgrees (st : SystemState) (w s : SeLe4n.ThreadId) :
    OffSchedulerAgrees st (st.linkReplyWaiter w s) :=
  .of_runLinkStep (by
      unfold SystemState.onlyObjectsSchedulerDiffer
      rw [SystemState.linkReplyWaiter_eq_objects st w s])
    (SystemState.linkReplyWaiter_objectsAgreeOffRunLinks st w s)

/-- WS-ZA ZA4.6: leaving a reply-waiter queue, likewise. -/
theorem unlinkReplyWaiter_offSchedulerAgrees (st : SystemState) (w s : SeLe4n.ThreadId) :
    OffSchedulerAgrees st (st.unlinkReplyWaiter w s) :=
  .of_runLinkStep (by
      unfold SystemState.onlyObjectsSchedulerDiffer
      rw [SystemState.unlinkReplyWaiter_eq_objects st w s])
    (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks st w s)

/-- WS-ZA ZA4.7: recording a blocking sender's badge and grant bit writes only
fields off the IPC read view. -/
theorem recordSendCap_offSchedulerAgrees (st : SystemState) (tid : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge) (grant : Bool) :
    OffSchedulerAgrees st (recordSendCap st tid badge grant) :=
  .of_runLinkStep (by unfold SystemState.onlyObjectsSchedulerDiffer; rfl)
    (recordSendCap_objectsAgreeOffRunLinks st tid badge grant)

/-- SM6.D: `removeRunnableOnCore` (the per-core dequeue) agrees with its
input off-scheduler. -/
theorem removeRunnableOnCore_offSchedulerAgrees (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    OffSchedulerAgrees st (removeRunnableOnCore st tid c) :=
  .of_runLinkStep (removeRunnableOnCore_onlyObjectsSchedulerDiffer st tid c)
    (removeRunnableOnCore_objectsAgreeOffRunLinks st tid c)

/-- **`v0.35.161`**: a replenishment migration is a scheduler-only update, or the
identity — it moves a SchedContext's CBS replenishments between two cores'
replenish queues and touches nothing else. -/
theorem migrateSchedContextReplenishment_offSchedulerAgrees (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) :
    OffSchedulerAgrees st (migrateSchedContextReplenishment st scId fromCore toCore) := by
  unfold migrateSchedContextReplenishment
  split
  · exact OffSchedulerAgrees.refl _
  · exact offSchedulerAgrees_scheduler_update _ _

/-- SM6.D: `enqueueRunnableOnCore` of an already-`.ready` thread agrees with
its input off-scheduler — the only object it writes is the woken TCB: its
`ipcState := .ready` is an identical-value re-insert and its run-queue links are
scheduler state; every other field is untouched. -/
theorem enqueueRunnableOnCore_offSchedulerAgrees_of_ready
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hInv : st.objects.invExt) :
    OffSchedulerAgrees st (enqueueRunnableOnCore st c tid) :=
  .of_runLinkStep (enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c tid)
    (enqueueRunnableOnCore_objectsAgreeOffRunLinks_of_ready st c tid tcb hTcb hReady hInv)

/-- SM6.D: the cross-core `wakeThread` of an already-`.ready` thread agrees
with its input off-scheduler. -/
theorem wakeThread_offSchedulerAgrees_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hInv : st.objects.invExt) :
    OffSchedulerAgrees st (wakeThread st tid ec).1 := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_offSchedulerAgrees_of_ready st _ tid tcb hTcb hReady hInv

-- ============================================================================
-- §4  Step congruences
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- SM6.D step congruence: `storeObject` of two objects that agree off the
run-queue links maps off-scheduler-agreeing inputs to off-scheduler-agreeing
outputs (it is total; control-free).  The kind, so the type-table entry and the
ASID side table, is the same on both sides. -/
theorem storeObject_offSchedulerAgrees_of_agree {s1 s2 r1 r2 : SystemState}
    (id : SeLe4n.ObjId) {o1 o2 : KernelObject}
    (ho : o2.withoutRunLinks = o1.withoutRunLinks)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h1 : storeObject id o1 s1 = .ok ((), r1))
    (h2 : storeObject id o2 s2 = .ok ((), r2)) :
    OffSchedulerAgrees r1 r2 := by
  have hObjEq : r2.objectsAgreeOffRunLinks r1 := by
    intro oid
    by_cases hEq : oid = id
    · rw [hEq, storeObject_objects_eq s2 r2 id o2 hInv2 h2,
          storeObject_objects_eq s1 r1 id o1 hInv1 h1]
      exact congrArg some ho
    · rw [storeObject_objects_ne s2 r2 id oid o2 hEq hInv2 h2,
          storeObject_objects_ne s1 r1 id oid o1 hEq hInv1 h1]
      exact hRel.objects oid
  rcases KernelObject.withoutRunLinks_eq_cases ho with rfl | ⟨t1, t2, rfl, rfl⟩
  all_goals
    unfold storeObject at h1 h2
    cases h1
    cases h2
    refine ⟨hObjEq, hRel.machine, ?_, ?_, hRel.services, hRel.irqHandlers, ?_, ?_,
      hRel.interfaceRegistry, hRel.serviceRegistry, hRel.cdt, hRel.tlb,
      hRel.perCoreTlb, hRel.perCoreICache, hRel.pendingIcacheMaintenance, hRel.pendingPhysicalWrites,
      hRel.declassificationAuditLog, hRel.declassificationAuditEpoch,
      hRel.declassificationRefusals, hRel.declassificationTaint⟩
    · simp only [hRel.objectIndexSet, hRel.objectIndex]
    · simp only [hRel.objectIndexSet]
    · simp only [hRel.lifecycle, KernelObject.objectType]
    · dsimp only
      -- the store keeps the ASID table alike on both sides: the same root at
      -- `id` and one ASID table, or a TCB, which never keeps it
      first
        | (rw [storeKeepsAsid_congr hRel.asidTable (fun _ =>
              ⟨hRel.objects.get_of_not_tcb' (fun _ e => KernelObject.noConfusion e),
               hRel.objects.get_of_not_tcb (fun _ e => KernelObject.noConfusion e)⟩),
            hRel.asidTable]
           split
           · rfl)
        | (simp only [storeKeepsAsid, Bool.false_eq_true, ↓reduceIte]
           rw [hRel.asidTable])
      cases e : s1.objects[id]? with
      | none => rw [hRel.objects.get_none_iff.mpr e]
      | some o => cases o with
        | tcb t => obtain ⟨t', h', _⟩ := hRel.objects.get_tcb e; rw [h']
        | _ => rw [hRel.objects.get_of_not_tcb (fun _ e => KernelObject.noConfusion e) e]


/-- Recording a Reply's stasher keeps two states that agree off the scheduler in
agreement: a Reply is the same object in both, so both record it or neither
does. -/
theorem recordReplyStasher_offSchedulerAgrees {s1 s2 : SystemState} (code : Nat)
    (recv : SeLe4n.ThreadId) (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt) :
    OffSchedulerAgrees (s1.recordReplyStasher code recv) (s2.recordReplyStasher code recv) := by
  rcases code with _ | k
  · exact hRel
  · by_cases hR : ∃ r, s1.objects[(⟨k⟩ : SeLe4n.ReplyId).toObjId]? = some (.reply r)
    · obtain ⟨r, e1⟩ := hR
      have e2 := hRel.objects.get_of_not_tcb (fun _ h => by cases h) e1
      exact storeObject_offSchedulerAgrees_of_agree _ rfl hRel hInv1 hInv2
        (SystemState.recordReplyStasher_of_reply s1 ⟨k⟩ recv e1)
        (SystemState.recordReplyStasher_of_reply s2 ⟨k⟩ recv e2)
    · have h1 : ∀ r, s1.objects[(⟨k⟩ : SeLe4n.ReplyId).toObjId]? ≠ some (.reply r) :=
        fun r e => hR ⟨r, e⟩
      have h2 : ∀ r, s2.objects[(⟨k⟩ : SeLe4n.ReplyId).toObjId]? ≠ some (.reply r) :=
        fun r e => h1 r (hRel.objects.get_of_not_tcb' (fun _ h => by cases h) e)
      rw [SystemState.recordReplyStasher_of_not_reply _ _ _ h1,
        SystemState.recordReplyStasher_of_not_reply _ _ _ h2]
      exact hRel
/-- SM6.D step congruence: `storeObject` of one object maps
off-scheduler-agreeing inputs to off-scheduler-agreeing outputs. -/
theorem storeObject_offSchedulerAgrees {s1 s2 r1 r2 : SystemState}
    (id : SeLe4n.ObjId) (obj : KernelObject)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h1 : storeObject id obj s1 = .ok ((), r1))
    (h2 : storeObject id obj s2 = .ok ((), r2)) :
    OffSchedulerAgrees r1 r2 :=
  storeObject_offSchedulerAgrees_of_agree id rfl hRel hInv1 hInv2 h1 h2

/-- WS-ZA ZA4.5: a TCB found in a store that agrees off the run-queue links is
the TCB of the other store with its run-queue fields rewritten. -/
theorem lookupTcb_back_of_objectsAgreeOffRunLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffRunLinks s1) {tid : SeLe4n.ThreadId} {t' : TCB}
    (hL : lookupTcb s2 tid = some t') :
    ∃ t : TCB, ∃ (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx rwp rwn rwh rwc : Nat) (ib : UInt64) (ibd icg ifs : Bool),
      lookupTcb s1 tid = some t ∧
      t' = { t with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                    runBucketPrevCode := rbpv, runBucketNextCode := rbnx,
                    replyWaiterPrevCode := rwp, replyWaiterNextCode := rwn,
                    replyWaitersHeadCode := rwh, replyWaitersCount := rwc,
                    ipcBadge := ib, ipcBadged := ibd, ipcCanGrant := icg, ipcFaultSend := ifs } := by
  unfold lookupTcb at hL ⊢
  cases hr : tid.isReserved
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at hL ⊢
    obtain ⟨t, rc, rp, rpv, rnx, rbpv, rbnx, rwp, rwn, rwh, rwc, ib, ibd, icg, ifs, ht, e⟩ :=
      h.get_tcb_back ((SystemState.getTcb?_eq_some_iff s2 tid t').mp hL)
    exact ⟨t, rc, rp, rpv, rnx, rbpv, rbnx, rwp, rwn, rwh, rwc, ib, ibd, icg, ifs, (SystemState.getTcb?_eq_some_iff s1 tid t).mpr ht, e⟩
  · simp only [hr, ↓reduceIte] at hL; cases hL

open SeLe4n.Model.SystemState in
/-- WS-ZA ZA4.4 step congruence: a `modifyTcb` whose rewrite reads no
run-queue field succeeds on the single-core-side state whenever it succeeds on
the cross-core-side state, with off-scheduler-agreeing outputs — one lookup the
relation fixes up to the run-queue links, one store that carries it. -/
theorem modifyTcb_offSchedulerAgrees {s1 s2 r2 : SystemState}
    (tid : SeLe4n.ThreadId) (f : TCB → TCB) (hf : TCB.RunLinksBlind f)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h2 : modifyTcb s2 tid f = .ok r2) :
    ∃ r1, modifyTcb s1 tid f = .ok r1 ∧ OffSchedulerAgrees r1 r2 := by
  unfold modifyTcb at h2 ⊢
  cases hL2 : lookupTcb s2 tid with
  | none => simp only [hL2] at h2; cases h2
  | some tcb2 =>
    obtain ⟨tcb, rc, rp, rpv, rnx, rbpv, rbnx, rwp, rwn, rwh, rwc, ib, ibd, icg, ifs, hL, hTcbEq⟩ :=
      lookupTcb_back_of_objectsAgreeOffRunLinks hRel.objects hL2
    simp only [hL2] at h2
    simp only [hL]
    cases hSO2 : storeObject tid.toObjId (.tcb (f tcb2)) s2 with
    | error e => simp only [hSO2] at h2; cases h2
    | ok p2 =>
      obtain ⟨⟨⟩, r2'⟩ := p2
      simp only [hSO2, Except.ok.injEq] at h2
      subst h2
      cases hSO1 : storeObject tid.toObjId (.tcb (f tcb)) s1 with
      | error e => exact absurd hSO1 (by unfold storeObject; simp)
      | ok p1 =>
        obtain ⟨⟨⟩, r1'⟩ := p1
        refine ⟨r1', rfl, storeObject_offSchedulerAgrees_of_agree _ ?_ hRel hInv1 hInv2 hSO1 hSO2⟩
        rw [hTcbEq]
        exact congrArg KernelObject.tcb (hf tcb rc rp rpv rnx rbpv rbnx rwp rwn rwh rwc ib ibd icg ifs)

/-- SM6.D step congruence: `storeTcbIpcStateAndMessage` succeeds on the
single-core-side state whenever it succeeds on the cross-core-side state,
with off-scheduler-agreeing outputs. -/
theorem storeTcbIpcStateAndMessage_offSchedulerAgrees {s1 s2 r2 : SystemState}
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h2 : storeTcbIpcStateAndMessage s2 tid ipc msg = .ok r2) :
    ∃ r1, storeTcbIpcStateAndMessage s1 tid ipc msg = .ok r1 ∧ OffSchedulerAgrees r1 r2 :=
  modifyTcb_offSchedulerAgrees tid _ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) hRel hInv1 hInv2 h2

/-- **`v0.35.161`** step congruence: `storeTcbQueueLinks` succeeds on the
single-core-side state whenever it succeeds on the cross-core-side state, with
off-scheduler-agreeing outputs — it is a `modifyTcb` of the queue links. -/
theorem storeTcbQueueLinks_offSchedulerAgrees {s1 s2 r2 : SystemState}
    (tid : SeLe4n.ThreadId) (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h2 : storeTcbQueueLinks s2 tid prev pprev next = .ok r2) :
    ∃ r1, storeTcbQueueLinks s1 tid prev pprev next = .ok r1 ∧ OffSchedulerAgrees r1 r2 :=
  modifyTcb_offSchedulerAgrees tid _ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) hRel hInv1 hInv2 h2

/-- WS-ZA ZA4.4 step congruence: the notification link-in — two `modifyTcb`
writes — carries the off-scheduler agreement. -/
theorem linkNtfnWaiter_offSchedulerAgrees {s1 s2 r2 : SystemState}
    (waiter : SeLe4n.ThreadId) (tail : Option SeLe4n.ThreadId)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h2 : linkNtfnWaiter s2 waiter tail = .ok r2) :
    ∃ r1, linkNtfnWaiter s1 waiter tail = .ok r1 ∧ OffSchedulerAgrees r1 r2 := by
  obtain ⟨m2, hM2, hR2⟩ := linkNtfnWaiter_ok_cases h2
  obtain ⟨m1, hM1, hRel1⟩ := modifyTcb_offSchedulerAgrees waiter _
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) hRel hInv1 hInv2 hM2
  have hInvM1 := modifyTcb_preserves_objects_invExt hInv1 hM1
  have hInvM2 := modifyTcb_preserves_objects_invExt hInv2 hM2
  unfold linkNtfnWaiter storeTcbNtfnLinks
  rw [hM1]
  unfold relinkNtfnNext modifyTcbOpt at hR2 ⊢
  cases tail with
  | none => cases hR2; exact ⟨m1, rfl, hRel1⟩
  | some t => exact modifyTcb_offSchedulerAgrees t _ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) hRel1 hInvM1 hInvM2 hR2

open SeLe4n.Model.SystemState in
/-- **`v0.35.161`** step congruence: `endpointQueueEnqueue` succeeds on the
single-core-side state whenever it succeeds on the cross-core-side state, with
off-scheduler-agreeing outputs.  Every read — the endpoint, the thread, the old
tail — goes through a lookup the relation fixes, so both spines take the same
branch, and each of the one to three stores carries the relation.

The receive leg needs it since `v0.35.161`: the two spines part at the
pre-receive donation return, whose cross-core form migrates the reservation's
replenishments (`cleanupPreReceiveDonationMigrated`), so from there on the
enqueue runs on two states that agree off the scheduler rather than on one. -/
theorem endpointQueueEnqueue_offSchedulerAgrees {s1 s2 r2 : SystemState}
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h2 : endpointQueueEnqueue endpointId isReceiveQ tid s2 = .ok r2) :
    ∃ r1, endpointQueueEnqueue endpointId isReceiveQ tid s1 = .ok r1 ∧
      OffSchedulerAgrees r1 r2 := by
  unfold endpointQueueEnqueue SystemState.getObject? at h2 ⊢
  revert h2
  cases hObj : s2.objects[endpointId]? with
  | none => simp
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _
    | reply _ | frame _ | pageTable _ => simp
    | endpoint ep =>
      rw [hRel.objects.get_endpoint_iff.mp hObj]
      simp only []
      cases hL2 : lookupTcb s2 tid with
      | none => simp
      | some tcb2 =>
        obtain ⟨tcb, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, rfl⟩ :=
          lookupTcb_back_of_objectsAgreeOffRunLinks hRel.objects hL2
        rw [hL]
        simp only []
        split
        · simp
        · split
          · simp
          · rename_i hClear
            rw [if_neg (show ¬ ((tcb.queuePPrev.isSome || tcb.queuePrev.isSome ||
              tcb.queueNext.isSome) = true) from hClear)]
            cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              simp only []
              cases hSO2 : storeObject endpointId
                  (.endpoint (if isReceiveQ
                    then (ep.withReceiveQ { head := some tid, tail := some tid })
                    else (ep.withSendQ { head := some tid, tail := some tid }))) s2 with
              | error e => simp
              | ok p2 =>
                obtain ⟨⟨⟩, t2⟩ := p2
                simp only []
                intro hLinks2
                cases hSO1 : storeObject endpointId
                    (.endpoint (if isReceiveQ
                      then (ep.withReceiveQ { head := some tid, tail := some tid })
                      else (ep.withSendQ { head := some tid, tail := some tid }))) s1 with
                | error e => exact absurd hSO1 (by unfold storeObject; simp)
                | ok p1 =>
                  obtain ⟨⟨⟩, t1⟩ := p1
                  simp only []
                  exact storeTcbQueueLinks_offSchedulerAgrees tid none (some .endpointHead) none
                    (storeObject_offSchedulerAgrees _ _ hRel hInv1 hInv2 hSO1 hSO2)
                    (storeObject_preserves_objects_invExt s1 t1 endpointId _ hInv1 hSO1)
                    (storeObject_preserves_objects_invExt s2 t2 endpointId _ hInv2 hSO2) hLinks2
            | some tailTid =>
              simp only []
              cases hLT2 : lookupTcb s2 tailTid with
              | none => simp
              | some tailTcb2 =>
                obtain ⟨tailTcb, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLT, hTailEq⟩ :=
                  lookupTcb_back_of_objectsAgreeOffRunLinks hRel.objects hLT2
                have hQP : tailTcb2.queuePrev = tailTcb.queuePrev := by subst hTailEq; rfl
                have hQPP : tailTcb2.queuePPrev = tailTcb.queuePPrev := by subst hTailEq; rfl
                rw [hLT]
                simp only [hQP, hQPP]
                cases hSO2 : storeObject endpointId
                    (.endpoint (if isReceiveQ
                      then (ep.withReceiveQ { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head, tail := some tid })
                      else (ep.withSendQ { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head, tail := some tid }))) s2 with
                | error e => simp
                | ok p2 =>
                  obtain ⟨⟨⟩, t2⟩ := p2
                  simp only []
                  cases hLinkT2 : storeTcbQueueLinks t2 tailTid tailTcb.queuePrev
                      tailTcb.queuePPrev (some tid) with
                  | error e => simp
                  | ok u2 =>
                    simp only []
                    intro hLinks2
                    cases hSO1 : storeObject endpointId
                        (.endpoint (if isReceiveQ
                          then (ep.withReceiveQ { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head, tail := some tid })
                          else (ep.withSendQ { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head, tail := some tid }))) s1 with
                    | error e => exact absurd hSO1 (by unfold storeObject; simp)
                    | ok p1 =>
                      obtain ⟨⟨⟩, t1⟩ := p1
                      simp only []
                      have hInvT1 : t1.objects.invExt :=
                        storeObject_preserves_objects_invExt s1 t1 endpointId _ hInv1 hSO1
                      have hInvT2 : t2.objects.invExt :=
                        storeObject_preserves_objects_invExt s2 t2 endpointId _ hInv2 hSO2
                      obtain ⟨u1, hLinkT1, hRelU⟩ :=
                        storeTcbQueueLinks_offSchedulerAgrees tailTid tailTcb.queuePrev
                          tailTcb.queuePPrev (some tid)
                          (storeObject_offSchedulerAgrees _ _ hRel hInv1 hInv2 hSO1 hSO2)
                          hInvT1 hInvT2 hLinkT2
                      rw [hLinkT1]
                      simp only []
                      exact storeTcbQueueLinks_offSchedulerAgrees tid (some tailTid)
                        (some (.tcbNext tailTid)) none hRelU
                        (storeTcbQueueLinks_preserves_objects_invExt t1 u1 tailTid _ _ _ hInvT1
                          hLinkT1)
                        (storeTcbQueueLinks_preserves_objects_invExt t2 u2 tailTid _ _ _ hInvT2
                          hLinkT2) hLinks2

open SeLe4n.Model.SystemState in
/-- SM6.D step congruence: `consumeReply` (total) maps off-scheduler-agreeing
inputs to off-scheduler-agreeing outputs. -/
theorem consumeReply_offSchedulerAgrees {s1 s2 r1 r2 : SystemState}
    (rid : SeLe4n.ReplyId)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h1 : consumeReply rid s1 = .ok ((), r1))
    (h2 : consumeReply rid s2 = .ok ((), r2)) :
    OffSchedulerAgrees r1 r2 := by
  unfold consumeReply at h1 h2
  rw [hRel.objects.getReply? rid] at h2
  cases hG : s1.getReply? rid with
  | none =>
      simp only [hG, Except.ok.injEq, Prod.mk.injEq, true_and] at h1 h2
      rw [← h1, ← h2]
      exact hRel
  | some r =>
      simp only [hG] at h1 h2
      exact storeObject_offSchedulerAgrees _ _ hRel hInv1 hInv2 h1 h2

open SeLe4n.Model.SystemState in
/-- **WS-HP HP6.4** step congruence for the removal's composed store step: two
states agreeing off the scheduler take the same branch of `spliceFrameBelow?` —
it reads `getReply?` and nothing else — and each of the one or three `storeObject`
writes carries the relation. -/
theorem spliceReplyFrameStores_offSchedulerAgrees {s1 s2 t1 t2 : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply}
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h1 : spliceReplyFrameStores s1 rid above r a = .ok t1)
    (h2 : spliceReplyFrameStores s2 rid above r a = .ok t2) :
    OffSchedulerAgrees t1 t2 := by
  have hGR : ∀ q, s2.getReply? q = s1.getReply? q :=
    fun q => hRel.objects.getReply? q
  have hBelow : spliceFrameBelow? s2 rid r above = spliceFrameBelow? s1 rid r above := by
    unfold spliceFrameBelow?
    cases hP : r.prev with
    | none => rfl
    | some below => simp only []; rw [hGR below]
  rcases spliceReplyFrameStores_cases h1 with ⟨hB1, hSa1⟩ |
    ⟨below, b, m1, n1, hB1, hSa1, hSb1, hSc1⟩
  · rcases spliceReplyFrameStores_cases h2 with ⟨_, hSa2⟩ | ⟨_, _, _, _, hB2, _, _, _⟩
    · exact storeObject_offSchedulerAgrees _ _ hRel hInv1 hInv2 hSa1 hSa2
    · rw [hBelow, hB1] at hB2; cases hB2
  · rcases spliceReplyFrameStores_cases h2 with ⟨hB2, _⟩ |
      ⟨below', b', m2, n2, hB2, hSa2, hSb2, hSc2⟩
    · rw [hBelow] at hB2; rw [hB1] at hB2; cases hB2
    · rw [hBelow, hB1, Option.some.injEq, Prod.mk.injEq] at hB2
      obtain ⟨rfl, rfl⟩ := hB2
      have hRelA : OffSchedulerAgrees m1 m2 :=
        storeObject_offSchedulerAgrees _ _ hRel hInv1 hInv2 hSa1 hSa2
      have hInvA1 := SeLe4n.Model.storeObject_preserves_objects_invExt s1 m1 _ _ hInv1 hSa1
      have hInvA2 := SeLe4n.Model.storeObject_preserves_objects_invExt s2 m2 _ _ hInv2 hSa2
      exact storeObject_offSchedulerAgrees _ _
        (storeObject_offSchedulerAgrees _ _ hRelA hInvA1 hInvA2 hSb1 hSb2)
        (SeLe4n.Model.storeObject_preserves_objects_invExt m1 n1 _ _ hInvA1 hSb1)
        (SeLe4n.Model.storeObject_preserves_objects_invExt m2 n2 _ _ hInvA2 hSb2) hSc1 hSc2

open SeLe4n.Model.SystemState in
/-- **WS-RM (`v0.35.6`)** step congruence: the removal's *splice* leg maps
off-scheduler-agreeing inputs to off-scheduler-agreeing outputs.  Its decision is
read off `getReply?` alone (`spliceReplyFrameOutOrSelf_decision`), so agreeing
object stores take the same branch; its writes are `storeObject`s, whose
congruence carries every other field. -/
theorem spliceReplyFrameOutOrSelf_offSchedulerAgrees {s1 s2 : SystemState}
    (rid : SeLe4n.ReplyId)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt) :
    OffSchedulerAgrees (spliceReplyFrameOutOrSelf s1 rid)
      (spliceReplyFrameOutOrSelf s2 rid) := by
  have hGR : ∀ q, s2.getReply? q = s1.getReply? q :=
    fun q => hRel.objects.getReply? q
  rcases spliceReplyFrameOutOrSelf_decision s1 rid with
    ⟨r1, above, a, hR1, hN1, hA1, hP1, hS1⟩ |
      ⟨r1, below, b, hR1, hN1, hPv1, hB1, hBn1, hS1⟩ | ⟨hId1, hNo1, hNoS1⟩
  · rcases spliceReplyFrameOutOrSelf_decision s2 rid with
      ⟨r2, above', a', hR2, hN2, hA2, _hP2, hS2⟩ |
        ⟨r2, _, _, hR2, hN2, _, _, _, _⟩ | ⟨_, hNo2, _⟩
    · have hRe : r2 = r1 := Option.some.inj (hR2.symm.trans ((hGR rid).trans hR1))
      subst hRe
      have hAb : above = above' := ReplyStackLink.frame.inj (Option.some.inj (hN1.symm.trans hN2))
      subst hAb
      have hAe : a' = a := Option.some.inj (hA2.symm.trans ((hGR above).trans hA1))
      subst hAe
      exact spliceReplyFrameStores_offSchedulerAgrees hRel hInv1 hInv2 hS1 hS2
    · have hRe : r2 = r1 := Option.some.inj (hR2.symm.trans ((hGR rid).trans hR1))
      subst hRe; rw [hN1] at hN2; cases hN2
    · exact absurd hP1 (hNo2 r1 above a ((hGR rid).trans hR1) hN1 ((hGR above).trans hA1))
  · rcases spliceReplyFrameOutOrSelf_decision s2 rid with
      ⟨r2, _, _, hR2, hN2, _, _, _⟩ |
        ⟨r2, below', b', hR2, hN2, hPv2, hB2, _, hS2⟩ | ⟨_, _, hNoS2⟩
    · have hRe : r2 = r1 := Option.some.inj (hR2.symm.trans ((hGR rid).trans hR1))
      subst hRe; rw [hN1] at hN2; cases hN2
    · have hRe : r2 = r1 := Option.some.inj (hR2.symm.trans ((hGR rid).trans hR1))
      subst hRe
      rw [hPv1] at hPv2; cases hPv2
      have hBe : b' = b := Option.some.inj (hB2.symm.trans ((hGR below).trans hB1))
      subst hBe
      obtain ⟨m1, hSa1, hSb1⟩ := severReplyFrameBelowStores_cases hS1
      obtain ⟨m2, hSa2, hSb2⟩ := severReplyFrameBelowStores_cases hS2
      exact storeObject_offSchedulerAgrees _ _
        (storeObject_offSchedulerAgrees _ _ hRel hInv1 hInv2 hSa1 hSa2)
        (SeLe4n.Model.storeObject_preserves_objects_invExt s1 m1 _ _ hInv1 hSa1)
        (SeLe4n.Model.storeObject_preserves_objects_invExt s2 m2 _ _ hInv2 hSa2) hSb1 hSb2
    · exact absurd hBn1 (hNoS2 r1 below b ((hGR rid).trans hR1) hN1 hPv1 ((hGR below).trans hB1))
  · rcases spliceReplyFrameOutOrSelf_decision s2 rid with
      ⟨r2, above, a, hR2, hN2, hA2, hP2, _⟩ |
        ⟨r2, below, b, hR2, hN2, hPv2, hB2, hBn2, _⟩ | ⟨hId2, _, _⟩
    · exact absurd hP2 (hNo1 r2 above a ((hGR rid).symm.trans hR2) hN2
        ((hGR above).symm.trans hA2))
    · exact absurd hBn2 (hNoS1 r2 below b ((hGR rid).symm.trans hR2) hN2 hPv2
        ((hGR below).symm.trans hB2))
    · rw [hId1, hId2]; exact hRel

open SeLe4n.Model.SystemState in
/-- SM6.D step congruence: `consumeCallerReply` (total) maps
off-scheduler-agreeing inputs to off-scheduler-agreeing outputs — the
reply-side `consumeReply` then the caller-side `replyObject` clear, both
lookup-determined. -/
theorem consumeCallerReply_offSchedulerAgrees {s1 s2 r1 r2 : SystemState}
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h1 : consumeCallerReply caller rid s1 = .ok ((), r1))
    (h2 : consumeCallerReply caller rid s2 = .ok ((), r2)) :
    OffSchedulerAgrees r1 r2 := by
  unfold SystemState.consumeCallerReply at h1 h2
  cases hC1 : consumeReply rid s1 with
  | error e => simp only [hC1] at h1; cases h1
  | ok p1 =>
    obtain ⟨⟨⟩, m1⟩ := p1
    cases hC2 : consumeReply rid s2 with
    | error e => simp only [hC2] at h2; cases h2
    | ok p2 =>
      obtain ⟨⟨⟩, m2⟩ := p2
      simp only [hC1] at h1
      simp only [hC2] at h2
      have hInvM1 : m1.objects.invExt := by
        unfold consumeReply at hC1
        cases hG : s1.getReply? rid with
        | none => rw [hG] at hC1; cases hC1; exact hInv1
        | some r =>
            rw [hG] at hC1
            exact storeObject_preserves_objects_invExt s1 m1 _ _ hInv1 hC1
      have hInvM2 : m2.objects.invExt := by
        unfold consumeReply at hC2
        cases hG : s2.getReply? rid with
        | none => rw [hG] at hC2; cases hC2; exact hInv2
        | some r =>
            rw [hG] at hC2
            exact storeObject_preserves_objects_invExt s2 m2 _ _ hInv2 hC2
      have hRelM : OffSchedulerAgrees m1 m2 := consumeReply_offSchedulerAgrees rid hRel hInv1 hInv2 hC1 hC2
      cases hG : m1.getTcb? caller with
      | none =>
          have hG2 : m2.getTcb? caller = none := by
            have := hRelM.objects.getTcb?_isSome caller
            rw [hG] at this
            cases e : m2.getTcb? caller with
            | none => rfl
            | some _ => rw [e] at this; cases this
          simp only [hG, hG2, Except.ok.injEq, Prod.mk.injEq, true_and] at h1 h2
          rw [← h1, ← h2]
          exact hRelM
      | some tcb =>
          obtain ⟨tcb2, hG2, e⟩ : ∃ t, m2.getTcb? caller = some t ∧
              t.withoutRunLinks = tcb.withoutRunLinks := by
            obtain ⟨t, ht, e⟩ := hRelM.objects.get_tcb ((getTcb?_eq_some_iff m1 caller tcb).mp hG)
            exact ⟨t, (getTcb?_eq_some_iff m2 caller t).mpr ht, e⟩
          simp only [hG] at h1
          simp only [hG2] at h2
          refine storeObject_offSchedulerAgrees_of_agree _ ?_ hRelM hInvM1 hInvM2 h1 h2
          rw [TCB.eq_withRunLinks_of_withoutRunLinks_eq e]
          rfl

open SeLe4n.Model.SystemState in
/-- **WS-RM (`v0.35.6`)** step congruence: the removal (total) maps
off-scheduler-agreeing inputs to off-scheduler-agreeing outputs — the splice,
then the consume.  This is what lets the cross-core reply's post-state be
compared with the single-core spine's now that both splice. -/
theorem removeCallerReplyFrame_offSchedulerAgrees {s1 s2 r1 r2 : SystemState}
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h1 : removeCallerReplyFrame caller rid s1 = .ok ((), r1))
    (h2 : removeCallerReplyFrame caller rid s2 = .ok ((), r2)) :
    OffSchedulerAgrees r1 r2 := by
  rw [removeCallerReplyFrame_eq] at h1 h2
  exact consumeCallerReply_offSchedulerAgrees caller rid
    (spliceReplyFrameOutOrSelf_offSchedulerAgrees rid hRel hInv1 hInv2)
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt s1 rid hInv1)
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt s2 rid hInv2) h1 h2

-- ============================================================================
-- §5  Read-view agreement: transports for transitions that rewrite only
--     objects the bundle never reads
-- ============================================================================

/-- Object kinds none of `ipcInvariantFull`'s queue, message, donation or reply
conjuncts read.  CNode *content* is read by exactly one clause —
`capabilityBadgesWellFormed` — which the master transport below therefore takes
as an explicit obligation for the target state; no conjunct reads a VSpaceRoot
or a piece of untyped memory at all — nor a **frame** (WS-BP BP7.1), which is a
page of memory a thread maps, not a structure any conjunct walks.  `none` is
deliberately **not** inert: a transition that deletes or creates an object of a
read kind must not slip through this frame, so only a rewrite that keeps the oid
on a non-read kind on *both* sides qualifies — and the one creation that is
sound, an absent key becoming a non-read kind, has its own lemma
(`of_fresh_inert_write`) rather than a widening of this predicate. -/
def ipcReadInert : Option KernelObject → Prop
  | some (.cnode _) => True
  | some (.vspaceRoot _) => True
  | some (.untyped _) => True
  | some (.frame _) => True
  | some (.pageTable _) => True
  | _ => False

/-- A run-queue clearing keeps a slot's binding view. -/
theorem notificationBindingCodes_map_withoutRunLinks (o : Option KernelObject) :
    notificationBindingCodes (o.map KernelObject.withoutRunLinks) =
      notificationBindingCodes o := by
  cases o with
  | none => rfl
  | some o => cases o <;> rfl

/-- A derivation-link clearing keeps a slot's binding view. -/
theorem notificationBindingCodes_map_withoutLinks (o : Option KernelObject) :
    notificationBindingCodes (o.map KernelObject.withoutLinks) =
      notificationBindingCodes o := by
  cases o with
  | none => rfl
  | some o => cases o <;> rfl

/-- An absent slot or one of a kind outside the read view holds no binding. -/
theorem notificationBindingCodes_of_absentOrInert {o : Option KernelObject}
    (h : o = none ∨ ipcReadInert o) : notificationBindingCodes o = (0, 0) := by
  rcases h with rfl | h
  · rfl
  · obtain _ | o := o
    · rfl
    · cases o <;> first | rfl | exact absurd h (by simp [ipcReadInert])

/-- A thread as every IPC bundle conjunct but the reciprocity reads it: the record
with its run-queue fields, its space-slot links and its bound-notification code
cleared.  The code is read by `notificationBindingReciprocal` alone, which the
whole-bundle transports take as its own hypothesis. -/
def _root_.SeLe4n.Model.TCB.ipcReadView (t : TCB) : TCB :=
  TCB.withoutLinks { TCB.withoutRunLinks t with boundNotificationCode := 0 }

/-- Two TCBs with the same IPC read view: the first is the second with its
run-queue fields, space-slot links and bound-notification code rewritten. -/
theorem _root_.SeLe4n.Model.TCB.eq_withIpcReadView_of_eq {t t' : TCB}
    (e : t'.ipcReadView = t.ipcReadView) :
    t' = { t with runCoreCode := t'.runCoreCode, runPrio := t'.runPrio,
                  runPrevCode := t'.runPrevCode, runNextCode := t'.runNextCode,
                  runBucketPrevCode := t'.runBucketPrevCode,
                  runBucketNextCode := t'.runBucketNextCode,
                  replyWaiterPrevCode := t'.replyWaiterPrevCode,
                  replyWaiterNextCode := t'.replyWaiterNextCode,
                  replyWaitersHeadCode := t'.replyWaitersHeadCode,
                  replyWaitersCount := t'.replyWaitersCount,
                  ipcBadge := t'.ipcBadge, ipcBadged := t'.ipcBadged,
                  ipcCanGrant := t'.ipcCanGrant, ipcFaultSend := t'.ipcFaultSend,
                  spaceLinks := t'.spaceLinks,
                  boundNotificationCode := t'.boundNotificationCode } := by
  cases t; cases t'
  simp only [TCB.ipcReadView, TCB.withoutRunLinks, TCB.withoutLinks, TCB.mk.injEq] at e ⊢
  simp only [e, and_self]

/-- Pointwise agreement on every object kind the IPC bundle's conjuncts read
through the store: TCBs, endpoints, notifications, replies and SchedContexts.
CNodes are deliberately absent — `capabilityBadgesWellFormed` is the one clause
that reads them, and the transitions this frame serves (capability writes,
page-table writes, untyped scrubs) exist precisely to rewrite them. -/
structure ipcReadViewAgreement (s1 s2 : SystemState) : Prop where
  /-- The TCB clauses are agreement **off the run-queue links** (WS-ZA ZA4.5)
  **and the space-slot links**: no conjunct reads the six run-queue fields,
  which are the scheduler's, nor a thread's derivation-link words, which are
  the tree's, so a run-queue or link write on either side stays inside the
  frame.  Nor does any of them read the bound-notification code: that is
  `notificationBindingReciprocal`'s, which the whole-bundle transports take
  separately, so a bind or unbind stays inside the frame too
  (`TCB.ipcReadView`). -/
  tcb : ∀ (oid : SeLe4n.ObjId) (t : TCB), s2.objects[oid]? = some (.tcb t) →
    ∃ t₀ : TCB, s1.objects[oid]? = some (.tcb t₀) ∧ t.ipcReadView = t₀.ipcReadView
  tcbFwd : ∀ (oid : SeLe4n.ObjId) (t₀ : TCB), s1.objects[oid]? = some (.tcb t₀) →
    ∃ t : TCB, s2.objects[oid]? = some (.tcb t) ∧ t.ipcReadView = t₀.ipcReadView
  endpoint : ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
    s2.objects[oid]? = some (.endpoint ep) ↔ s1.objects[oid]? = some (.endpoint ep)
  /-- The notification clause is *content* agreement, not value agreement:
  every notification-reading conjunct but the reciprocity reads `state`,
  `waitHead` and `pendingBadge` only, so a rewrite that moves `boundTCB` or the
  lock word — the `.tcbBindNotification` arms — stays inside the frame. -/
  notification : ∀ (oid : SeLe4n.ObjId) (ntfn : Notification),
    s2.objects[oid]? = some (.notification ntfn) →
    ∃ ntfn₀ : Notification, s1.objects[oid]? = some (.notification ntfn₀) ∧
      ntfn₀.state = ntfn.state ∧ ntfn₀.waitHead = ntfn.waitHead ∧
      ntfn₀.pendingBadge = ntfn.pendingBadge
  reply : ∀ (oid : SeLe4n.ObjId) (r : SeLe4n.Kernel.Reply),
    s2.objects[oid]? = some (.reply r) ↔ s1.objects[oid]? = some (.reply r)
  /-- The SchedContext clause is likewise *content* agreement, stated in the
  `s1 → s2` direction the transports consume: the bundle reads only an SC's
  existence and its `boundThread`, so budget, period, priority, deadline and
  domain rewrites — the `.schedContextConfigure` and priority arms — stay
  inside the frame. -/
  schedContext : ∀ (oid : SeLe4n.ObjId) (sc : SeLe4n.Kernel.SchedContext),
    s1.objects[oid]? = some (.schedContext sc) →
    ∃ sc' : SeLe4n.Kernel.SchedContext, s2.objects[oid]? = some (.schedContext sc') ∧
      sc'.boundThread = sc.boundThread

namespace sameNotificationBindings

/-- Stores that agree off the run-queue links hold the same binding codes. -/
theorem of_objectsAgreeOffRunLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffRunLinks s1) : sameNotificationBindings s1 s2 := fun x => by
  rw [← notificationBindingCodes_map_withoutRunLinks, h x,
    notificationBindingCodes_map_withoutRunLinks]

/-- Stores that agree off the derivation links hold the same binding codes. -/
theorem of_objectsAgreeOffDerivationLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffDerivationLinks s1) : sameNotificationBindings s1 s2 := fun x => by
  rw [← notificationBindingCodes_map_withoutLinks, (h x).map_withoutLinks,
    notificationBindingCodes_map_withoutLinks]

/-- Rewrites that keep every rewritten key absent or outside the read view, on
each side, move no binding code. -/
theorem of_inertOrAbsentWrites {s1 s2 : SystemState}
    (h : ∀ oid : SeLe4n.ObjId,
      s2.objects[oid]? = s1.objects[oid]? ∨
      ((s1.objects[oid]? = none ∨ ipcReadInert s1.objects[oid]?) ∧
       (s2.objects[oid]? = none ∨ ipcReadInert s2.objects[oid]?))) :
    sameNotificationBindings s1 s2 := fun oid => by
  rcases h oid with hEq | ⟨h1, h2⟩
  · rw [hEq]
  · rw [notificationBindingCodes_of_absentOrInert h1,
      notificationBindingCodes_of_absentOrInert h2]

/-- Rewrites inert on both sides move no binding code. -/
theorem of_inertWrites {s1 s2 : SystemState}
    (h : ∀ oid : SeLe4n.ObjId,
      s2.objects[oid]? = s1.objects[oid]? ∨
      (ipcReadInert s1.objects[oid]? ∧ ipcReadInert s2.objects[oid]?)) :
    sameNotificationBindings s1 s2 :=
  of_inertOrAbsentWrites fun oid => (h oid).imp id fun ⟨h1, h2⟩ => ⟨.inr h1, .inr h2⟩

/-- One rewritten slot, inert on both sides. -/
theorem of_single_inert_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (h1 : ipcReadInert s1.objects[key]?) (h2 : ipcReadInert s2.objects[key]?) :
    sameNotificationBindings s1 s2 :=
  of_inertWrites fun oid => by
    by_cases hEq : oid = key
    · subst hEq; exact Or.inr ⟨h1, h2⟩
    · exact Or.inl (hNe oid hEq)

/-- An absent key made a non-read kind. -/
theorem of_fresh_inert_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (h1 : s1.objects[key]? = none) (h2 : ipcReadInert s2.objects[key]?) :
    sameNotificationBindings s1 s2 :=
  of_inertOrAbsentWrites fun oid => by
    by_cases hEq : oid = key
    · subst hEq; exact Or.inr ⟨.inl h1, .inr h2⟩
    · exact Or.inl (hNe oid hEq)

/-- One slot rewritten to an object with the slot's codes. -/
theorem of_single_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (hKey : notificationBindingCodes s2.objects[key]? = notificationBindingCodes s1.objects[key]?) :
    sameNotificationBindings s1 s2 := fun oid => by
  by_cases hEq : oid = key
  · subst hEq; exact hKey
  · rw [hNe oid hEq]

/-- One SchedContext rewritten: a SchedContext holds no binding code. -/
theorem of_schedContext_content_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    {sc sc' : SeLe4n.Kernel.SchedContext}
    (hPre : s1.objects[key]? = some (.schedContext sc))
    (hAt : s2.objects[key]? = some (.schedContext sc'))
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (_hBound : sc'.boundThread = sc.boundThread) :
    sameNotificationBindings s1 s2 :=
  of_single_write hNe (by rw [hAt, hPre]; rfl)

end sameNotificationBindings

namespace ipcReadViewAgreement

/-- **WS-ZA ZA4.5**: object stores that agree off the run-queue links are
read-view agreement — the relation a run-queue write induces. -/
theorem of_objectsAgreeOffRunLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffRunLinks s1) : ipcReadViewAgreement s1 s2 :=
  ⟨fun _ _ hx => (h.get_tcb' hx).elim fun t ht =>
     ⟨t, ht.1, congrArg (fun u : TCB => TCB.withoutLinks { u with boundNotificationCode := 0 }) ht.2⟩,
   fun _ _ hx => (h.get_tcb hx).elim fun t ht =>
     ⟨t, ht.1, congrArg (fun u : TCB => TCB.withoutLinks { u with boundNotificationCode := 0 }) ht.2⟩,
   fun _ _ => h.get_endpoint_iff,
   fun _ ntfn hObj => ⟨ntfn, h.get_notification_iff.mp hObj, rfl, rfl, rfl⟩,
   fun _ _ => h.get_reply_iff,
   fun _ sc hSc => ⟨sc, h.get_schedContext_iff.mpr hSc, rfl⟩⟩

/-- Object stores that agree off the derivation links are read-view agreement:
a CNode is outside the view, and a thread differs only in its space-slot links. -/
theorem of_objectsAgreeOffDerivationLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffDerivationLinks s1) : ipcReadViewAgreement s1 s2 :=
  ⟨fun _ _ hx => (h.tcb_back hx).elim fun t ht =>
     ⟨t, ht.1, congrArg (fun u : TCB => { TCB.withoutRunLinks u with boundNotificationCode := 0 }) ht.2⟩,
   fun _ _ hx => (h.tcb_fwd hx).elim fun t ht =>
     ⟨t, ht.1, congrArg (fun u : TCB => { TCB.withoutRunLinks u with boundNotificationCode := 0 }) ht.2⟩,
   fun _ _ => h.obj_iff (fun _ e => KernelObject.noConfusion e),
   fun _ ntfn hObj =>
     ⟨ntfn, h.obj_back hObj (fun _ e => KernelObject.noConfusion e), rfl, rfl, rfl⟩,
   fun _ _ => h.obj_iff (fun _ e => KernelObject.noConfusion e),
   fun _ sc hSc => ⟨sc, h.obj_fwd hSc (fun _ e => KernelObject.noConfusion e), rfl⟩⟩

/-- Full pointwise lookup agreement is read-view agreement. -/
theorem of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?) :
    ipcReadViewAgreement s1 s2 :=
  of_objectsAgreeOffRunLinks (.of_getElem_eq hEq)

/-- The frame the capability, VSpace and untyped-scrub transitions induce:
lookups agree except at rewritten oids, and every rewritten oid holds a kind
outside the read view in **both** states. -/
theorem of_inertWrites {s1 s2 : SystemState}
    (h : ∀ oid : SeLe4n.ObjId,
      s2.objects[oid]? = s1.objects[oid]? ∨
      (ipcReadInert s1.objects[oid]? ∧ ipcReadInert s2.objects[oid]?)) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), ¬ ipcReadInert (some o) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNotInert
    rcases h oid with hEq | ⟨h1, h2⟩
    · rw [hEq]
    · constructor
      · intro hx; rw [hx] at h2; exact absurd h2 hNotInert
      · intro hx; rw [hx] at h1; exact absurd h1 hNotInert
  exact ⟨fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mp h, rfl⟩,
         fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mpr h, rfl⟩,
         fun oid ep => step oid (.endpoint ep) (by simp [ipcReadInert]),
         fun oid ntfn hObj =>
           ⟨ntfn, (step oid (.notification ntfn) (by simp [ipcReadInert])).mp hObj,
             rfl, rfl, rfl⟩,
         fun oid r => step oid (.reply r) (by simp [ipcReadInert]),
         fun oid sc hSc =>
           ⟨sc, (step oid (.schedContext sc) (by simp [ipcReadInert])).mpr hSc, rfl⟩⟩

/-- The single-oid instance: one rewritten slot, inert on both sides — the
shape of every CNode-slot write and every page-table update. -/
theorem of_single_inert_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (h1 : ipcReadInert s1.objects[key]?) (h2 : ipcReadInert s2.objects[key]?) :
    ipcReadViewAgreement s1 s2 :=
  of_inertWrites fun oid => by
    by_cases hEq : oid = key
    · subst hEq; exact Or.inr ⟨h1, h2⟩
    · exact Or.inl (hNe oid hEq)

/-- **WS-BP BP7.1**: the creation instance — a key that held **no** object and
now holds one of a non-read kind.  Sound for the reason `ipcReadInert` excludes
`none` on both sides: a read-kind lookup is `some` of that kind, which neither an
absent key nor a non-read object is, so every read-kind lookup agrees.  The shape
of the frame an untyped carve creates. -/
theorem of_fresh_inert_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (h1 : s1.objects[key]? = none) (h2 : ipcReadInert s2.objects[key]?) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), ¬ ipcReadInert (some o) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNotInert
    by_cases hK : oid = key
    · subst hK
      rw [h1]
      constructor
      · intro hx; rw [hx] at h2; exact absurd h2 hNotInert
      · intro hx; cases hx
    · rw [hNe oid hK]
  exact ⟨fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mp h, rfl⟩,
         fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mpr h, rfl⟩,
         fun oid ep => step oid (.endpoint ep) (by simp [ipcReadInert]),
         fun oid ntfn hObj =>
           ⟨ntfn, (step oid (.notification ntfn) (by simp [ipcReadInert])).mp hObj,
             rfl, rfl, rfl⟩,
         fun oid r => step oid (.reply r) (by simp [ipcReadInert]),
         fun oid sc hSc =>
           ⟨sc, (step oid (.schedContext sc) (by simp [ipcReadInert])).mpr hSc, rfl⟩⟩

/-- **WS-BP BP7.1 slice 3**: the general form of the two instances above — every
rewritten key holds, on **each** side independently, either nothing or a kind
outside the read view.  Covers creation (absent → inert), rewriting (inert →
inert) and **erasure** (inert → absent) at once, which is the shape an untyped
reset induces: VSpace roots rewritten, frames erased, the untyped rewritten. -/
theorem of_inertOrAbsentWrites {s1 s2 : SystemState}
    (h : ∀ oid : SeLe4n.ObjId,
      s2.objects[oid]? = s1.objects[oid]? ∨
      ((s1.objects[oid]? = none ∨ ipcReadInert s1.objects[oid]?) ∧
       (s2.objects[oid]? = none ∨ ipcReadInert s2.objects[oid]?))) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), ¬ ipcReadInert (some o) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNotInert
    rcases h oid with hEq | ⟨h1, h2⟩
    · rw [hEq]
    · constructor
      · intro hx; rw [hx] at h2
        rcases h2 with h2 | h2
        · cases h2
        · exact absurd h2 hNotInert
      · intro hx; rw [hx] at h1
        rcases h1 with h1 | h1
        · cases h1
        · exact absurd h1 hNotInert
  exact ⟨fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mp h, rfl⟩,
         fun oid t h => ⟨t, (step oid (.tcb t) (by simp [ipcReadInert])).mpr h, rfl⟩,
         fun oid ep => step oid (.endpoint ep) (by simp [ipcReadInert]),
         fun oid ntfn hObj =>
           ⟨ntfn, (step oid (.notification ntfn) (by simp [ipcReadInert])).mp hObj,
             rfl, rfl, rfl⟩,
         fun oid r => step oid (.reply r) (by simp [ipcReadInert]),
         fun oid sc hSc =>
           ⟨sc, (step oid (.schedContext sc) (by simp [ipcReadInert])).mpr hSc, rfl⟩⟩

/-- A single notification rewrite preserving queue content — `state`,
`waitHead`, `pendingBadge`; `boundTCB`, the tail and the lock word are free —
is read-view agreement.  The `.tcbBindNotification` /
`.tcbUnbindNotification` arms' notification store is exactly this shape. -/
theorem of_notification_content_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    {ntfn ntfn' : Notification}
    (hPre : s1.objects[key]? = some (.notification ntfn))
    (hAt : s2.objects[key]? = some (.notification ntfn'))
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (hState : ntfn'.state = ntfn.state)
    (hWaiters : ntfn'.waitHead = ntfn.waitHead)
    (hBadge : ntfn'.pendingBadge = ntfn.pendingBadge) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject),
      (∀ n : Notification, o ≠ .notification n) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNo
    by_cases hK : oid = key
    · subst hK
      rw [hPre, hAt]
      constructor
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo ntfn')
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo ntfn)
    · rw [hNe oid hK]
  refine ⟨fun oid t h => ⟨t, (step oid (.tcb t) (fun n h => KernelObject.noConfusion h)).mp h, rfl⟩,
          fun oid t h => ⟨t, (step oid (.tcb t) (fun n h => KernelObject.noConfusion h)).mpr h, rfl⟩,
          fun oid ep => step oid (.endpoint ep) (fun n h => KernelObject.noConfusion h),
          fun oid n hObj => ?_,
          fun oid r => step oid (.reply r) (fun n h => KernelObject.noConfusion h),
          fun oid sc hSc =>
            ⟨sc, (step oid (.schedContext sc)
              (fun n h => KernelObject.noConfusion h)).mpr hSc, rfl⟩⟩
  by_cases hK : oid = key
  · subst hK
    rw [hAt] at hObj
    obtain rfl : ntfn' = n := by
      simpa only [Option.some.injEq, KernelObject.notification.injEq] using hObj
    exact ⟨ntfn, hPre, hState.symm, hWaiters.symm, hBadge.symm⟩
  · rw [hNe oid hK] at hObj
    exact ⟨n, hObj, rfl, rfl, rfl⟩

/-- A single TCB rewrite that keeps the thread's IPC read view — run links,
space-slot links and the bound-notification code are free — is read-view
agreement.  The bind and unbind arms' thread store is exactly this shape. -/
theorem of_tcb_ipcReadView_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    {t t' : TCB}
    (hPre : s1.objects[key]? = some (.tcb t))
    (hAt : s2.objects[key]? = some (.tcb t'))
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (hView : t'.ipcReadView = t.ipcReadView) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), (∀ x : TCB, o ≠ .tcb x) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNo
    by_cases hK : oid = key
    · subst hK
      rw [hPre, hAt]
      constructor
      · intro hx; exact absurd (Option.some.inj hx).symm (hNo t')
      · intro hx; exact absurd (Option.some.inj hx).symm (hNo t)
    · rw [hNe oid hK]
  refine ⟨fun oid x h => ?_, fun oid x h => ?_,
          fun oid ep => step oid (.endpoint ep) (fun _ h => KernelObject.noConfusion h),
          fun oid n hObj =>
            ⟨n, (step oid (.notification n) (fun _ h => KernelObject.noConfusion h)).mp hObj,
              rfl, rfl, rfl⟩,
          fun oid r => step oid (.reply r) (fun _ h => KernelObject.noConfusion h),
          fun oid sc hSc =>
            ⟨sc, (step oid (.schedContext sc) (fun _ h => KernelObject.noConfusion h)).mpr hSc,
              rfl⟩⟩
  · by_cases hK : oid = key
    · subst hK
      rw [hAt] at h; cases h
      exact ⟨t, hPre, hView⟩
    · rw [hNe oid hK] at h; exact ⟨x, h, rfl⟩
  · by_cases hK : oid = key
    · subst hK
      rw [hPre] at h; cases h
      exact ⟨t', hAt, hView⟩
    · exact ⟨x, by rw [hNe oid hK]; exact h, rfl⟩

/-- A single SchedContext rewrite preserving `boundThread` — budget, period,
priority, deadline, domain and the lock word are free — is read-view
agreement.  The `.schedContextConfigure` arm's store and the priority arms'
SC-priority update are exactly this shape. -/
theorem of_schedContext_content_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    {sc sc' : SeLe4n.Kernel.SchedContext}
    (hPre : s1.objects[key]? = some (.schedContext sc))
    (hAt : s2.objects[key]? = some (.schedContext sc'))
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (hBound : sc'.boundThread = sc.boundThread) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject),
      (∀ x : SeLe4n.Kernel.SchedContext, o ≠ .schedContext x) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNo
    by_cases hK : oid = key
    · subst hK
      rw [hPre, hAt]
      constructor
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo sc')
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo sc)
    · rw [hNe oid hK]
  refine ⟨fun oid t h => ⟨t, (step oid (.tcb t) (fun x h => KernelObject.noConfusion h)).mp h, rfl⟩,
          fun oid t h => ⟨t, (step oid (.tcb t) (fun x h => KernelObject.noConfusion h)).mpr h, rfl⟩,
          fun oid ep => step oid (.endpoint ep) (fun x h => KernelObject.noConfusion h),
          fun oid n hObj =>
            ⟨n, (step oid (.notification n)
              (fun x h => KernelObject.noConfusion h)).mp hObj, rfl, rfl, rfl⟩,
          fun oid r => step oid (.reply r) (fun x h => KernelObject.noConfusion h),
          fun oid x hSc => ?_⟩
  by_cases hK : oid = key
  · subst hK
    rw [hPre] at hSc
    obtain rfl : sc = x := by
      simpa only [Option.some.injEq, KernelObject.schedContext.injEq] using hSc
    exact ⟨sc', hAt, hBound⟩
  · rw [← hNe oid hK] at hSc
    exact ⟨x, hSc, rfl⟩

/-- Read-view agreement composes. -/
theorem trans {s1 s2 s3 : SystemState}
    (hFore : ipcReadViewAgreement s1 s2) (hAft : ipcReadViewAgreement s2 s3) :
    ipcReadViewAgreement s1 s3 :=
  ⟨fun oid t h3 => by
     obtain ⟨t2, h2, e2⟩ := hAft.tcb oid t h3
     obtain ⟨t1, h1, e1⟩ := hFore.tcb oid t2 h2
     exact ⟨t1, h1, e2.trans e1⟩,
   fun oid t h1 => by
     obtain ⟨t2, h2, e2⟩ := hFore.tcbFwd oid t h1
     obtain ⟨t3, h3, e3⟩ := hAft.tcbFwd oid t2 h2
     exact ⟨t3, h3, e3.trans e2⟩,
   fun oid ep => (hAft.endpoint oid ep).trans (hFore.endpoint oid ep),
   fun oid n h3 => by
     obtain ⟨n2, h2, hS2, hW2, hB2⟩ := hAft.notification oid n h3
     obtain ⟨n1, h1, hS1, hW1, hB1⟩ := hFore.notification oid n2 h2
     exact ⟨n1, h1, hS1.trans hS2, hW1.trans hW2, hB1.trans hB2⟩,
   fun oid r => (hAft.reply oid r).trans (hFore.reply oid r),
   fun oid sc h1 => by
     obtain ⟨sc2, h2, hB2⟩ := hFore.schedContext oid sc h1
     obtain ⟨sc3, h3, hB3⟩ := hAft.schedContext oid sc2 h2
     exact ⟨sc3, h3, hB3.trans hB2⟩⟩

/-- A TCB of `s2` is a TCB of `s1` with its run-queue fields rewritten — the
form `run_links_back` substitutes. -/
theorem get_tcb_back {s1 s2 : SystemState} (hView : ipcReadViewAgreement s1 s2)
    {x : SeLe4n.ObjId} {t' : TCB} (hx : s2.objects[x]? = some (.tcb t')) :
    ∃ t : TCB, ∃ (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx rwp rwn rwh rwc : Nat) (ib : UInt64) (ibd icg ifs : Bool)
      (sl : Vector Nat (slotLinkWords * 2)) (bnc : Nat),
      s1.objects[x]? = some (.tcb t) ∧
      t' = { t with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                    runBucketPrevCode := rbpv, runBucketNextCode := rbnx,
                    replyWaiterPrevCode := rwp, replyWaiterNextCode := rwn,
                    replyWaitersHeadCode := rwh, replyWaitersCount := rwc,
                    ipcBadge := ib, ipcBadged := ibd, ipcCanGrant := icg, ipcFaultSend := ifs,
                    spaceLinks := sl, boundNotificationCode := bnc } := by
  obtain ⟨t, ht, e⟩ := hView.tcb x t' hx
  exact ⟨t, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, TCB.eq_withIpcReadView_of_eq e⟩

/-- The same, from `s1` to `s2` — the form `run_links_fwd` substitutes. -/
theorem get_tcb_fwd {s1 s2 : SystemState} (hView : ipcReadViewAgreement s1 s2)
    {x : SeLe4n.ObjId} {t : TCB} (hx : s1.objects[x]? = some (.tcb t)) :
    ∃ t' : TCB, ∃ (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx rwp rwn rwh rwc : Nat) (ib : UInt64) (ibd icg ifs : Bool)
      (sl : Vector Nat (slotLinkWords * 2)) (bnc : Nat),
      s2.objects[x]? = some (.tcb t') ∧
      t = { t' with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                    runBucketPrevCode := rbpv, runBucketNextCode := rbnx,
                    replyWaiterPrevCode := rwp, replyWaiterNextCode := rwn,
                    replyWaitersHeadCode := rwh, replyWaitersCount := rwc,
                    ipcBadge := ib, ipcBadged := ibd, ipcCanGrant := icg, ipcFaultSend := ifs,
                    spaceLinks := sl, boundNotificationCode := bnc } := by
  obtain ⟨t', ht, e⟩ := hView.tcbFwd x t hx
  exact ⟨t', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, TCB.eq_withIpcReadView_of_eq e.symm⟩

/-- The typed-getter form of the reply clause. -/
theorem getReply?_iff {s1 s2 : SystemState} (hView : ipcReadViewAgreement s1 s2)
    (rid : SeLe4n.ReplyId) (r : SeLe4n.Kernel.Reply) :
    s2.getReply? rid = some r ↔ s1.getReply? rid = some r :=
  (SystemState.getReply?_eq_some_iff s2 rid r).trans
    ((hView.reply rid.toObjId r).trans (SystemState.getReply?_eq_some_iff s1 rid r).symm)

end ipcReadViewAgreement

/-- Read-view transport of a `queueNext` reachability path. -/
theorem QueueNextPath_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) {a b : SeLe4n.ThreadId}
    (hp : QueueNextPath s2 a b) : QueueNextPath s1 a b := by
  induction hp with
  | single x y tcbA hObj hNext =>
    run_links_back hView at tcbA hObj
    exact .single x y tcbA hObj hNext
  | cons x y z tcbA hObj hNext _ ih =>
    run_links_back hView at tcbA hObj
    exact .cons x y z tcbA hObj hNext ih

/-- **WS-RR RR8.3**: read-view transport of the pairing.  The view's `tcb`
clause is full-record agreement, so the pair travels with the record. -/
theorem queuePPrevAgreesWithPrev_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) (h : queuePPrevAgreesWithPrev s1) :
    queuePPrevAgreesWithPrev s2 :=
  fun tid tcb hTcb => by
    run_links_back hView at tcb hTcb
    exact h tid tcb hTcb

/-- Read-view transport of TCB-queue chain acyclicity. -/
theorem tcbQueueChainAcyclic_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : tcbQueueChainAcyclic s1) : tcbQueueChainAcyclic s2 :=
  fun tid hp => h tid (QueueNextPath_of_readViewAgreement hView hp)

/-- Read-view transport of doubly-linked TCB-queue link integrity. -/
theorem tcbQueueLinkIntegrity_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : tcbQueueLinkIntegrity s1) : tcbQueueLinkIntegrity s2 := by
  obtain ⟨hFwd, hRev⟩ := h
  refine ⟨fun a tcbA hA b hNext => ?_, fun b tcbB hB a hPrev => ?_⟩
  · run_links_back hView at tcbA hA
    obtain ⟨tcbB, hB, hPrev⟩ := hFwd a tcbA hA b hNext
    run_links_fwd hView at tcbB hB
    exact ⟨_, hB, hPrev⟩
  · run_links_back hView at tcbB hB
    obtain ⟨tcbA, hA, hNext⟩ := hRev b tcbB hB a hPrev
    run_links_fwd hView at tcbA hA
    exact ⟨_, hA, hNext⟩

/-- Read-view transport of single-queue well-formedness. -/
theorem intrusiveQueueWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) {q : IntrusiveQueue}
    (h : intrusiveQueueWellFormed q s1) : intrusiveQueueWellFormed q s2 := by
  obtain ⟨hP1, hP2, hP3⟩ := h
  refine ⟨hP1, fun hd hHead => ?_, fun tl hTail => ?_⟩
  · obtain ⟨tcb, hObj, hPrev⟩ := hP2 hd hHead
    run_links_fwd hView at tcb hObj
    exact ⟨_, hObj, hPrev⟩
  · obtain ⟨tcb, hObj, hNext⟩ := hP3 tl hTail
    run_links_fwd hView at tcb hObj
    exact ⟨_, hObj, hNext⟩

/-- Read-view transport of an endpoint's dual-queue well-formedness. -/
theorem dualQueueEndpointWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) {epId : SeLe4n.ObjId}
    (h : dualQueueEndpointWellFormed epId s1) : dualQueueEndpointWellFormed epId s2 := by
  unfold dualQueueEndpointWellFormed at h ⊢
  cases hObj : s2.objects[epId]? with
  | none => trivial
  | some obj =>
    cases obj with
    | endpoint ep =>
      rw [(hView.endpoint _ _).mp hObj] at h
      exact ⟨intrusiveQueueWellFormed_of_readViewAgreement hView h.1,
             intrusiveQueueWellFormed_of_readViewAgreement hView h.2⟩
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ =>
      trivial

/-- Read-view transport of the dual-queue system invariant. -/
theorem dualQueueSystemInvariant_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : dualQueueSystemInvariant s1) : dualQueueSystemInvariant s2 := by
  obtain ⟨hEp, hLink, hAcyc, hPP, hHD⟩ := h
  refine ⟨fun epId ep hObj => ?_,
          tcbQueueLinkIntegrity_of_readViewAgreement hView hLink,
          tcbQueueChainAcyclic_of_readViewAgreement hView hAcyc,
          queuePPrevAgreesWithPrev_of_readViewAgreement hView hPP,
          -- **PR #897 review**: the read view agrees on endpoints, which is all the
          -- fifth conjunct reads.
          endpointQueueHeadDisjoint_of_endpointBackward
            (fun epId ep hEp' => by rw [hView.endpoint] at hEp'; exact hEp') hHD⟩
  rw [hView.endpoint] at hObj
  exact dualQueueEndpointWellFormed_of_readViewAgreement hView (hEp epId ep hObj)

/-- Read-view transport of pending-message boundedness. -/
theorem allPendingMessagesBounded_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : allPendingMessagesBounded s1) : allPendingMessagesBounded s2 := by
  intro tid tcb msg hObj hPend
  run_links_back hView at tcb hObj
  exact h tid tcb msg hObj hPend

/-- Read-view transport of the generic in-flight-message family. -/
theorem pendingMessagesSatisfy_of_readViewAgreement {P : IpcMessage → Prop} {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : pendingMessagesSatisfy P s1) : pendingMessagesSatisfy P s2 := by
  intro tid tcb msg hObj hPend
  run_links_back hView at tcb hObj
  exact h tid tcb msg hObj hPend

/-- Read-view transport of the notification half of `badgeWellFormed`. -/
theorem notificationBadgesWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : notificationBadgesWellFormed s1) : notificationBadgesWellFormed s2 := by
  intro oid ntfn badge hObj hBadge
  obtain ⟨ntfn₀, hL, _, _, hB⟩ := hView.notification oid ntfn hObj
  exact h oid ntfn₀ badge hL (hB.trans hBadge)

/-- Read-view transport of notification well-formedness. -/
theorem ipcInvariant_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : ipcInvariant s1) : ipcInvariant s2 := by
  intro oid ntfn hObj
  obtain ⟨ntfn₀, hL, hS, hW, hB⟩ := hView.notification oid ntfn hObj
  have h₀ := h oid ntfn₀ hL
  unfold notificationInvariant notificationQueueWellFormed at h₀ ⊢
  rw [← hS, ← hW, ← hB]
  exact h₀

/-- Read-view transport of `blockedThreadsPendingMessageConsistent`. -/
theorem blockedThreadsPendingMessageConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : blockedThreadsPendingMessageConsistent s1) :
    blockedThreadsPendingMessageConsistent s2 := by
  intro tid tcb hObj
  run_links_back hView at tcb hObj
  exact h tid tcb hObj

/-- Read-view transport of `endpointQueueNoDup`. -/
theorem endpointQueueNoDup_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : endpointQueueNoDup s1) : endpointQueueNoDup s2 := by
  intro oid ep hEp
  rw [hView.endpoint] at hEp
  obtain ⟨hSelf, hDisj⟩ := h oid ep hEp
  refine ⟨fun tid tcb hTcb => ?_, hDisj⟩
  run_links_back hView at tcb hTcb
  exact hSelf tid tcb hTcb

/-- Read-view transport of `ipcStateQueueMembershipConsistent`. -/
theorem ipcStateQueueMembershipConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : ipcStateQueueMembershipConsistent s1) : ipcStateQueueMembershipConsistent s2 := by
  intro tid tcb hTcb
  run_links_back hView at tcb hTcb
  have hG := h tid tcb hTcb
  cases hIpc : tcb.ipcState with
  | blockedOnSend epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, (hView.endpoint _ _).mpr hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · run_links_fwd hView at prevTcb hPrev
        exact Or.inr ⟨prev, _, hPrev, hNext⟩
  | blockedOnReceive epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, (hView.endpoint _ _).mpr hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · run_links_fwd hView at prevTcb hPrev
        exact Or.inr ⟨prev, _, hPrev, hNext⟩
  | blockedOnCall epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, (hView.endpoint _ _).mpr hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · run_links_fwd hView at prevTcb hPrev
        exact Or.inr ⟨prev, _, hPrev, hNext⟩
  | ready => trivial
  | blockedOnNotification nid => trivial
  | blockedOnReply ep rt => trivial

/-- Read-view transport of `queueNextBlockingConsistent`. -/
theorem queueNextBlockingConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : queueNextBlockingConsistent s1) : queueNextBlockingConsistent s2 := by
  intro a b tcbA tcbB hA hB hNext
  run_links_back hView at tcbA hA; run_links_back hView at tcbB hB
  exact h a b tcbA tcbB hA hB hNext

/-- Read-view transport of `queueHeadBlockedConsistent`. -/
theorem queueHeadBlockedConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : queueHeadBlockedConsistent s1) : queueHeadBlockedConsistent s2 := by
  intro epId ep hd tcb hEp hTcb
  rw [hView.endpoint] at hEp
  run_links_back hView at tcb hTcb
  exact h epId ep hd tcb hEp hTcb

/-- Read-view transport of `blockedThreadTimeoutConsistent`. -/
theorem blockedThreadTimeoutConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : blockedThreadTimeoutConsistent s1) : blockedThreadTimeoutConsistent s2 := by
  intro tid tcb scId hTcb hBudget
  run_links_back hView at tcb hTcb
  obtain ⟨⟨sc, hSc⟩, hBlk⟩ := h tid tcb scId hTcb hBudget
  obtain ⟨sc', hSc', _⟩ := hView.schedContext _ sc hSc
  exact ⟨⟨sc', hSc'⟩, hBlk⟩

/-- Read-view transport of `allTimeoutBudgetsNone`. -/
theorem allTimeoutBudgetsNone_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : allTimeoutBudgetsNone s1) : allTimeoutBudgetsNone s2 := by
  intro tid tcb hTcb
  run_links_back hView at tcb hTcb
  exact h tid tcb hTcb

/-- Read-view transport of `donationChainAcyclic`. -/
theorem donationChainAcyclic_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationChainAcyclic s1) : donationChainAcyclic s2 := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
  run_links_back hView at tcb1 h1; run_links_back hView at tcb2 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2

/-- Read-view transport of `donationOwnerValid`. -/
theorem donationOwnerValid_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationOwnerValid s1) : donationOwnerValid s2 := by
  intro tid tcb scId owner hTcb hBind
  run_links_back hView at tcb hTcb
  obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOwner, hUnbound, hReply⟩⟩ :=
    h tid tcb scId owner hTcb hBind
  obtain ⟨sc', hSc', hBT⟩ := hView.schedContext _ sc hSc
  run_links_fwd hView at ownerTcb hOwner
  exact ⟨⟨sc', hSc', hBT.trans hBound⟩, ⟨_, hOwner, hUnbound, hReply⟩⟩

/-- Read-view transport of `donationBudgetTransfer`. -/
theorem donationBudgetTransfer_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationBudgetTransfer s1) : donationBudgetTransfer s2 := by
  intro tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2
  run_links_back hView at tcb1 h1; run_links_back hView at tcb2 h2
  exact h tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2

/-- Read-view transport of `blockedOnReplyHasTarget`. -/
theorem blockedOnReplyHasTarget_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : blockedOnReplyHasTarget s1) : blockedOnReplyHasTarget s2 := by
  intro tid tcb endpointId replyTarget hTcb hIpc
  run_links_back hView at tcb hTcb
  exact h tid tcb endpointId replyTarget hTcb hIpc

/-- Read-view transport of `replyCallerLinkageReciprocal`. -/
theorem replyCallerLinkageReciprocal_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : replyCallerLinkageReciprocal s1) : replyCallerLinkageReciprocal s2 := by
  refine ⟨fun tid tcb rid hTcb hRep => ?_, fun rid r tid hRep hCaller => ?_⟩
  · run_links_back hView at tcb hTcb
    obtain ⟨r, hR, hBack⟩ := h.1 tid tcb rid hTcb hRep
    exact ⟨r, (hView.reply _ _).mpr hR, hBack⟩
  · rw [hView.reply] at hRep
    obtain ⟨tcb, hTcb, hFwd, hBlk⟩ := h.2 rid r tid hRep hCaller
    run_links_fwd hView at tcb hTcb
    exact ⟨_, hTcb, hFwd, hBlk⟩

/-- Read-view transport of `blockedOnReplyHasReplyObject`. -/
theorem blockedOnReplyHasReplyObject_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : blockedOnReplyHasReplyObject s1) : blockedOnReplyHasReplyObject s2 := by
  intro tid tcb ep rt hTcb hIpc
  run_links_back hView at tcb hTcb
  exact h tid tcb ep rt hTcb hIpc

/-- Read-view transport of `replyCallerLinkage`. -/
theorem replyCallerLinkage_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : replyCallerLinkage s1) : replyCallerLinkage s2 :=
  ⟨replyCallerLinkageReciprocal_of_readViewAgreement hView h.1,
   blockedOnReplyHasReplyObject_of_readViewAgreement hView h.2⟩

/-- Read-view transport of `pendingReceiveReplyWellFormed`. -/
theorem pendingReceiveReplyWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : pendingReceiveReplyWellFormed s1) : pendingReceiveReplyWellFormed s2 := by
  refine ⟨fun tid tcb rid hTcb hStash => ?_,
          fun tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hS1 hS2 => ?_,
          fun tid tcb rid hTcb hStash => ?_⟩
  · rw [SystemState.getTcb?_eq_some_iff] at hTcb
    run_links_back hView at tcb hTcb
    rw [← SystemState.getTcb?_eq_some_iff] at hTcb
    obtain ⟨hRecv, ⟨r, hR, hFree⟩⟩ := h.1 tid tcb rid hTcb hStash
    exact ⟨hRecv, ⟨r, (hView.getReply?_iff _ _).mpr hR, hFree⟩⟩
  · rw [SystemState.getTcb?_eq_some_iff] at h1 h2
    run_links_back hView at tcb₁ h1; run_links_back hView at tcb₂ h2
    rw [← SystemState.getTcb?_eq_some_iff] at h1 h2
    exact h.2.1 tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hS1 hS2
  · rw [SystemState.getTcb?_eq_some_iff] at hTcb
    run_links_back hView at tcb hTcb
    rw [← SystemState.getTcb?_eq_some_iff] at hTcb
    obtain ⟨r, hR, hS⟩ := h.2.2 tid tcb rid hTcb hStash
    exact ⟨r, (hView.getReply?_iff _ _).mpr hR, hS⟩

/-- Read-view transport of `donationOwnerUnique`. -/
theorem donationOwnerUnique_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationOwnerUnique s1) : donationOwnerUnique s2 := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
  run_links_back hView at tcb1 h1; run_links_back hView at tcb2 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2

/-- Read-view transport of `endpointQueueTailBlockedConsistent`. -/
theorem endpointQueueTailBlockedConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : endpointQueueTailBlockedConsistent s1) : endpointQueueTailBlockedConsistent s2 := by
  intro epId ep tl tcb hEp hTcb
  rw [hView.endpoint] at hEp
  run_links_back hView at tcb hTcb
  exact h epId ep tl tcb hEp hTcb

/-- Read-view transport of `queueNextTargetBlocked`. -/
theorem queueNextTargetBlocked_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : queueNextTargetBlocked s1) : queueNextTargetBlocked s2 := by
  intro a b tcbA tcbB hA hB hNext
  run_links_back hView at tcbA hA; run_links_back hView at tcbB hB
  exact h a b tcbA tcbB hA hB hNext

/-- **The read-view master transport**: two states agreeing on every object
kind the bundle reads satisfy the eighteen conjuncts that read neither a CNode
nor a binding code interchangeably; the CNode-reading clause
(`capabilityBadgesWellFormed`) and the binding reciprocity are supplied for the
target state.  This is the lever that carries the whole bundle across the
capability, VSpace and untyped-scrub dispatch arms, whose writes the bundle
never reads, and across the bind and unbind arms, whose writes only the
reciprocity reads. -/
theorem ipcInvariantFull_of_readViewAgreement_of_reciprocal {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (hCapBadges : capabilityBadgesWellFormed s2)
    (hNBR : notificationBindingReciprocal s2)
    (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ⟨ipcInvariant_of_readViewAgreement hView h.ipcInvariant,
   dualQueueSystemInvariant_of_readViewAgreement hView h.dualQueueSystemInvariant,
   allPendingMessagesBounded_of_readViewAgreement hView h.allPendingMessagesBounded,
   ⟨notificationBadgesWellFormed_of_readViewAgreement hView h.badgeWellFormed.1, hCapBadges⟩,
   blockedThreadsPendingMessageConsistent_of_readViewAgreement hView
     h.blockedThreadsPendingMessageConsistent,
   endpointQueueNoDup_of_readViewAgreement hView h.endpointQueueNoDup,
   ipcStateQueueMembershipConsistent_of_readViewAgreement hView
     h.ipcStateQueueMembershipConsistent,
   queueNextBlockingConsistent_of_readViewAgreement hView h.queueNextBlockingConsistent,
   queueHeadBlockedConsistent_of_readViewAgreement hView h.queueHeadBlockedConsistent,
   blockedThreadTimeoutConsistent_of_readViewAgreement hView h.blockedThreadTimeoutConsistent,
   donationChainAcyclic_of_readViewAgreement hView h.donationChainAcyclic,
   donationOwnerValid_of_readViewAgreement hView h.donationOwnerValid,
   donationBudgetTransfer_of_readViewAgreement hView h.donationBudgetTransfer,
   blockedOnReplyHasTarget_of_readViewAgreement hView h.blockedOnReplyHasTarget,
   replyCallerLinkage_of_readViewAgreement hView h.replyCallerLinkage,
   pendingReceiveReplyWellFormed_of_readViewAgreement hView h.pendingReceiveReplyWellFormed,
   donationOwnerUnique_of_readViewAgreement hView h.donationOwnerUnique,
   endpointQueueTailBlockedConsistent_of_readViewAgreement hView
     h.endpointQueueTailBlockedConsistent,
   queueNextTargetBlocked_of_readViewAgreement hView h.queueNextTargetBlocked,
   hNBR⟩

/-- The master transport for a write that moves no binding code: the
reciprocity carries with the codes. -/
theorem ipcInvariantFull_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (hCodes : sameNotificationBindings s1 s2)
    (hCapBadges : capabilityBadgesWellFormed s2)
    (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ipcInvariantFull_of_readViewAgreement_of_reciprocal hView hCapBadges
    (.of_codes hCodes h.notificationBindingReciprocal) h

/-- WS-ZA ZA4.5: object slots read the same in stores that agree off the
run-queue links, so the capability half of `badgeWellFormed` carries across them. -/
theorem capabilityBadgesWellFormed_of_objectsAgreeOffRunLinks {s1 s2 : SystemState}
    (hA : s2.objectsAgreeOffRunLinks s1) (h : capabilityBadgesWellFormed s1) :
    capabilityBadgesWellFormed s2 :=
  capabilityBadgesWellFormed_of_slotCap_back h fun _ _ hO =>
    let ⟨o, ho, hs, _⟩ := hA.slots_back hO; ⟨o, ho, hs⟩


/-- WS-SM SM6.D, restated for WS-ZA ZA4.5: **the whole-bundle transport** —
two states whose object stores agree off the run-queue links satisfy the
twenty conjuncts of `ipcInvariantFull` interchangeably.  This is the lever that carries the single-core whole-bundle
theorems across the cross-core wake, whose run-queue placement differs. -/
theorem ipcInvariantFull_of_objectsAgreeOffRunLinks {s1 s2 : SystemState}
    (hA : s2.objectsAgreeOffRunLinks s1)
    (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ipcInvariantFull_of_readViewAgreement (.of_objectsAgreeOffRunLinks hA)
    (.of_objectsAgreeOffRunLinks hA) (capabilityBadgesWellFormed_of_objectsAgreeOffRunLinks hA h.badgeWellFormed.2) h

/-- The same for pointwise-equal lookups. -/
theorem ipcInvariantFull_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ipcInvariantFull_of_objectsAgreeOffRunLinks (.of_getElem_eq hEq) h

/-- WS-RR RR3.12: read-view transport of the relaxed donation-owner invariant. -/
theorem donationOwnerValidExcept_of_readViewAgreement {s1 s2 : SystemState}
    {woken : SeLe4n.ThreadId}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationOwnerValidExcept s1 woken) : donationOwnerValidExcept s2 woken := by
  intro tid tcb scId owner hTcb hBind
  run_links_back hView at tcb hTcb
  obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOwner, hUnbound, hCase⟩⟩ :=
    h tid tcb scId owner hTcb hBind
  obtain ⟨sc', hSc', hBT⟩ := hView.schedContext _ sc hSc
  run_links_fwd hView at ownerTcb hOwner
  exact ⟨⟨sc', hSc', hBT.trans hBound⟩, ⟨_, hOwner, hUnbound, hCase⟩⟩

/-- WS-RR RR3.12: the relaxed bundle transports across stores that agree off
the run-queue links, exactly as `ipcInvariantFull_of_objectsAgreeOffRunLinks`
does for the full one. -/
theorem ipcInvariantFullExceptDonationOwner_of_objectsAgreeOffRunLinks {s1 s2 : SystemState}
    {woken : SeLe4n.ThreadId}
    (hA : s2.objectsAgreeOffRunLinks s1)
    (h : ipcInvariantFullExceptDonationOwner s1 woken) :
    ipcInvariantFullExceptDonationOwner s2 woken := by
  have hView : ipcReadViewAgreement s1 s2 := .of_objectsAgreeOffRunLinks hA
  exact ⟨ipcInvariant_of_readViewAgreement hView h.1,
   dualQueueSystemInvariant_of_readViewAgreement hView h.2.1,
   allPendingMessagesBounded_of_readViewAgreement hView h.2.2.1,
   badgeWellFormed_of_objectsAgreeOffRunLinks hA h.2.2.2.1,
   blockedThreadsPendingMessageConsistent_of_readViewAgreement hView h.2.2.2.2.1,
   endpointQueueNoDup_of_readViewAgreement hView h.2.2.2.2.2.1,
   ipcStateQueueMembershipConsistent_of_readViewAgreement hView h.2.2.2.2.2.2.1,
   queueNextBlockingConsistent_of_readViewAgreement hView h.2.2.2.2.2.2.2.1,
   queueHeadBlockedConsistent_of_readViewAgreement hView h.2.2.2.2.2.2.2.2.1,
   blockedThreadTimeoutConsistent_of_readViewAgreement hView h.2.2.2.2.2.2.2.2.2.1,
   donationChainAcyclic_of_readViewAgreement hView h.2.2.2.2.2.2.2.2.2.2.1,
   donationOwnerValidExcept_of_readViewAgreement hView h.donationOwnerValidExcept,
   donationBudgetTransfer_of_readViewAgreement hView h.2.2.2.2.2.2.2.2.2.2.2.2.1,
   blockedOnReplyHasTarget_of_readViewAgreement hView h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   replyCallerLinkage_of_readViewAgreement hView h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   pendingReceiveReplyWellFormed_of_readViewAgreement hView
     h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   donationOwnerUnique_of_readViewAgreement hView h.donationOwnerUnique,
   endpointQueueTailBlockedConsistent_of_readViewAgreement hView
     h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   queueNextTargetBlocked_of_readViewAgreement hView h.queueNextTargetBlocked,
   .of_codes (.of_objectsAgreeOffRunLinks hA) h.notificationBindingReciprocal⟩

/-- The transition frame nearly every capability-only dispatch arm induces:
objects untouched.  `ipcInvariantFull` reads nothing else, so it transports
whole. -/
theorem ipcInvariantFull_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects)
    (h : ipcInvariantFull st) : ipcInvariantFull st' :=
  ipcInvariantFull_of_getElem_eq (fun _ => by rw [hObjs])
    h

end SeLe4n.Kernel
