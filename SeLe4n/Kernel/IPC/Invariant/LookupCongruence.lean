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
import SeLe4n.Kernel.Scheduler.SchedulerLinkFrame
import SeLe4n.Kernel.IPC.Invariant.ReadViewAgreement

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
  /-- WS-ZA ZA4.5 / ZA6.3: objects agree **off the scheduler links** — the
      run-queue links, scheduler state that lives in the TCB, and the release-queue
      links, scheduler state that lives in the scheduling context. -/
  objects : s2.objectsAgreeOffSchedulerLinks s1
  machine : s2.machine = s1.machine
  objectIndex : s2.objectIndex = s1.objectIndex
  objectIndexSet : s2.objectIndexSet = s1.objectIndexSet
  irqSignalLines : s2.irqSignalLines = s1.irqSignalLines
  lifecycle : s2.lifecycle = s1.lifecycle
  asidTable : s2.asidTable = s1.asidTable
  interfaceRegistry : s2.interfaceRegistry = s1.interfaceRegistry
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

namespace OffSchedulerAgrees

/-- Reflexivity. -/
theorem refl (st : SystemState) : OffSchedulerAgrees st st :=
  ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Symmetry. -/
theorem symm {s1 s2 : SystemState} (h : OffSchedulerAgrees s1 s2) :
    OffSchedulerAgrees s2 s1 :=
  ⟨h.objects.symm, h.machine.symm, h.objectIndex.symm,
   h.objectIndexSet.symm, h.irqSignalLines.symm, h.lifecycle.symm,
   h.asidTable.symm, h.interfaceRegistry.symm, h.cdt.symm,
   h.tlb.symm, h.perCoreTlb.symm, h.perCoreICache.symm,
   h.pendingIcacheMaintenance.symm, h.pendingPhysicalWrites.symm, h.declassificationAuditLog.symm,
   h.declassificationAuditEpoch.symm, h.declassificationRefusals.symm⟩

/-- Transitivity. -/
theorem trans {s1 s2 s3 : SystemState}
    (hFirst : OffSchedulerAgrees s1 s2) (hSecond : OffSchedulerAgrees s2 s3) :
    OffSchedulerAgrees s1 s3 :=
  ⟨hSecond.objects.trans hFirst.objects, hSecond.machine.trans hFirst.machine,
   hSecond.objectIndex.trans hFirst.objectIndex, hSecond.objectIndexSet.trans hFirst.objectIndexSet,
   hSecond.irqSignalLines.trans hFirst.irqSignalLines,
   hSecond.lifecycle.trans hFirst.lifecycle, hSecond.asidTable.trans hFirst.asidTable,
   hSecond.interfaceRegistry.trans hFirst.interfaceRegistry,
   hSecond.cdt.trans hFirst.cdt,
   hSecond.tlb.trans hFirst.tlb,
   hSecond.perCoreTlb.trans hFirst.perCoreTlb, hSecond.perCoreICache.trans hFirst.perCoreICache,
   hSecond.pendingIcacheMaintenance.trans hFirst.pendingIcacheMaintenance,
   hSecond.pendingPhysicalWrites.trans hFirst.pendingPhysicalWrites,
   hSecond.declassificationAuditLog.trans hFirst.declassificationAuditLog,
   hSecond.declassificationAuditEpoch.trans hFirst.declassificationAuditEpoch,
   hSecond.declassificationRefusals.trans hFirst.declassificationRefusals⟩

/-- The two states carry the same bookkeeping ghosts: the object index, its
membership set and the recorded object kinds all agree. -/
theorem ghostsKept {s1 s2 : SystemState} (h : OffSchedulerAgrees s1 s2)
    (hC : s1.objects.capacity ≤ s2.objects.capacity) : SystemState.ghostsKept s2 s1 :=
  ⟨h.objectIndex, h.objectIndexSet, by rw [h.lifecycle], hC, by rw [h.asidTable]; exact Nat.le_refl _⟩

/-- WS-SM SM9.D.5: **the declassification taint agrees** — the provenance
analogue of the trail and ledger clauses, and load-bearing for the same reason:
a scheduler substitution that silently re-keyed an object's taint would move a
recorded downgrade's causal ancestry.  Since WS-ZA ZA5.12 the taint is read off
the objects' words, which the run-queue fields do not hold, so the objects
clause carries it. -/
theorem declassificationTaint {s1 s2 : SystemState} (h : OffSchedulerAgrees s1 s2) :
    s2.declassificationTaint = s1.declassificationTaint :=
  h.objects.declassificationTaint

end OffSchedulerAgrees

-- ============================================================================
-- §3  Scheduler-substitution agreements
-- ============================================================================

/-- WS-ZA ZA4.5: a step that writes only the object store and the scheduler,
and the store only off the run-queue links, agrees with its input
off-scheduler. -/
theorem OffSchedulerAgrees.of_runLinkStep {st st' : SystemState}
    (hD : st'.onlyObjectsSchedulerDiffer st) (hA : st'.objectsAgreeOffRunLinks st) :
    OffSchedulerAgrees st st' := by
  have hD' := hD
  unfold SystemState.onlyObjectsSchedulerDiffer at hD'
  refine ⟨.of_runLinks hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hD']; try rfl)

/-- WS-ZA ZA6.3: a step that writes only the release queues — the object store
off the release-queue links and the scheduler's release slots — agrees with its
input off-scheduler. -/
theorem OffSchedulerAgrees.of_releaseStep {st st' : SystemState}
    (hW : st'.releaseOnlyWrite st) (hA : st'.objectsAgreeOffReleaseLinks st) :
    OffSchedulerAgrees st st' := by
  have hD' := hW.1
  refine ⟨.of_releaseLinks hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hD']; try rfl)

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

/-- WS-ZA ZA6.34: leaving the queue of the server a reply wait names, if it
names one (a caller its server's finalisation forgot is on none). -/
theorem unlinkReplyWaiterOpt_offSchedulerAgrees (st : SystemState) (w : SeLe4n.ThreadId)
    (s? : Option SeLe4n.ThreadId) :
    OffSchedulerAgrees st (st.unlinkReplyWaiterOpt w s?) := by
  cases s? with
  | none => exact OffSchedulerAgrees.refl st
  | some s => exact unlinkReplyWaiter_offSchedulerAgrees st w s

/-- WS-ZA ZA4.7: recording a blocking sender's badge and grant bit writes only
fields off the IPC read view. -/
theorem recordSendCap_offSchedulerAgrees (st : SystemState) (tid : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge) (grant grantReply : Bool) :
    OffSchedulerAgrees st (recordSendCap st tid badge grant grantReply) :=
  .of_runLinkStep (by unfold SystemState.onlyObjectsSchedulerDiffer; rfl)
    (recordSendCap_objectsAgreeOffRunLinks st tid badge grant grantReply)

/-- SM6.D: `removeRunnableOnCore` (the per-core dequeue) agrees with its
input off-scheduler. -/
theorem removeRunnableOnCore_offSchedulerAgrees (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    OffSchedulerAgrees st (removeRunnableOnCore st tid c) :=
  .of_runLinkStep (removeRunnableOnCore_onlyObjectsSchedulerDiffer st tid c)
    (removeRunnableOnCore_objectsAgreeOffRunLinks st tid c)

/-- **`v0.35.161`**: a replenishment migration is a scheduler-only update, or the
identity — it moves a SchedContext's CBS replenishments between two cores'
release queues, writing the release-queue links and touching nothing else
(WS-ZA ZA6.3). -/
theorem migrateSchedContextReplenishment_offSchedulerAgrees (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) :
    OffSchedulerAgrees st (migrateSchedContextReplenishment st scId fromCore toCore) :=
  .of_releaseStep (migrateSchedContextReplenishment_releaseOnlyWrite st scId fromCore toCore)
    (migrateSchedContextReplenishment_agree st scId fromCore toCore)

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
  have hObjEq : r2.objectsAgreeOffSchedulerLinks r1 := by
    intro oid
    by_cases hEq : oid = id
    · rw [hEq, storeObject_objects_eq s2 r2 id o2 hInv2 h2,
          storeObject_objects_eq s1 r1 id o1 hInv1 h1]
      show some o2.withoutRunLinks.withoutRelease = some o1.withoutRunLinks.withoutRelease
      rw [ho]
    · rw [storeObject_objects_ne s2 r2 id oid o2 hEq hInv2 h2,
          storeObject_objects_ne s1 r1 id oid o1 hEq hInv1 h1]
      exact hRel.objects oid
  rcases KernelObject.withoutRunLinks_eq_cases ho with rfl | ⟨t1, t2, rfl, rfl⟩
  all_goals
    unfold storeObject at h1 h2
    cases h1
    cases h2
    refine ⟨hObjEq, hRel.machine, ?_, ?_, hRel.irqSignalLines, ?_, ?_,
      hRel.interfaceRegistry, hRel.cdt, hRel.tlb,
      hRel.perCoreTlb, hRel.perCoreICache, hRel.pendingIcacheMaintenance, hRel.pendingPhysicalWrites,
      hRel.declassificationAuditLog, hRel.declassificationAuditEpoch,
      hRel.declassificationRefusals⟩
    · have hS := objects_isSome_of_getObjectType? (hRel.objects.getObjectType? id)
      simp only [SystemState.objectIndex, hS]
      split
      · exact hRel.objectIndex
      · simp only [SeLe4n.Erased.out_mk]; exact congrArg (id :: ·) hRel.objectIndex
    · have hS := objects_isSome_of_getObjectType? (hRel.objects.getObjectType? id)
      simp only [SystemState.objectIndexSet, hS]
      split
      · exact hRel.objectIndexSet
      · simp only [SeLe4n.Erased.out_mk]; exact congrArg (·.insert id) hRel.objectIndexSet
    · rw [storeKeepsKind_of_getObjectType? (hRel.objects.getObjectType? id)]
      simp only [hRel.lifecycle, KernelObject.objectType]
    · dsimp only
      -- the store keeps the ASID table alike on both sides: the same root at
      -- `id` and one ASID table, or a TCB, which never keeps it
      first
        | (rw [storeKeepsAsid_congr hRel.asidTable (fun _ =>
              ⟨hRel.objects.get_of_plain' (fun _ e => KernelObject.noConfusion e)
                 (fun _ e => KernelObject.noConfusion e),
               hRel.objects.get_of_plain (fun _ e => KernelObject.noConfusion e)
                 (fun _ e => KernelObject.noConfusion e)⟩),
            hRel.asidTable]
           split
           · rfl)
        | (simp only [storeKeepsAsid, Bool.false_eq_true, ↓reduceIte]
           rw [hRel.asidTable])
      cases e : s1.objects[id]? with
      | none => rw [hRel.objects.get_none_iff.mpr e]
      | some o => cases o with
        | tcb t => obtain ⟨t', h', _⟩ := hRel.objects.get_tcb e; rw [h']
        | schedContext sc => obtain ⟨sc', h', _⟩ := hRel.objects.get_sc e; rw [h']
        | _ => rw [hRel.objects.get_of_plain (fun _ e => KernelObject.noConfusion e)
            (fun _ e => KernelObject.noConfusion e) e]


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
      have e2 := hRel.objects.get_of_plain (fun _ h => by cases h) (fun _ h => by cases h) e1
      exact storeObject_offSchedulerAgrees_of_agree _ rfl hRel hInv1 hInv2
        (SystemState.recordReplyStasher_of_reply s1 ⟨k⟩ recv e1)
        (SystemState.recordReplyStasher_of_reply s2 ⟨k⟩ recv e2)
    · have h1 : ∀ r, s1.objects[(⟨k⟩ : SeLe4n.ReplyId).toObjId]? ≠ some (.reply r) :=
        fun r e => hR ⟨r, e⟩
      have h2 : ∀ r, s2.objects[(⟨k⟩ : SeLe4n.ReplyId).toObjId]? ≠ some (.reply r) :=
        fun r e => h1 r (hRel.objects.get_of_plain' (fun _ h => by cases h) (fun _ h => by cases h) e)
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

/-- WS-ZA ZA4.5 / ZA6.3: a TCB found in a store that agrees off the scheduler links
is the TCB of the other store with its run-queue fields rewritten. -/
theorem lookupTcb_back_of_objectsAgreeOffSchedulerLinks {s1 s2 : SystemState}
    (h : s2.objectsAgreeOffSchedulerLinks s1) {tid : SeLe4n.ThreadId} {t' : TCB}
    (hL : lookupTcb s2 tid = some t') :
    ∃ t : TCB, ∃ (rc : Nat) (rp : SeLe4n.Priority) (rpv rnx rbpv rbnx rwp rwn rwh rwc : Nat) (ib : UInt64) (ibd icg icgr ifs : Bool),
      lookupTcb s1 tid = some t ∧
      t' = { t with runCoreCode := rc, runPrio := rp, runPrevCode := rpv, runNextCode := rnx,
                    runBucketPrevCode := rbpv, runBucketNextCode := rbnx,
                    replyWaiterPrevCode := rwp, replyWaiterNextCode := rwn,
                    replyWaitersHeadCode := rwh, replyWaitersCount := rwc,
                    ipcBadge := ib, ipcBadged := ibd, ipcCanGrant := icg, ipcCanGrantReply := icgr, ipcFaultSend := ifs } := by
  unfold lookupTcb at hL ⊢
  cases hr : tid.isReserved
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at hL ⊢
    obtain ⟨t, rc, rp, rpv, rnx, rbpv, rbnx, rwp, rwn, rwh, rwc, ib, ibd, icg, icgr, ifs, ht, e⟩ :=
      h.get_tcb_back ((SystemState.getTcb?_eq_some_iff s2 tid t').mp hL)
    exact ⟨t, rc, rp, rpv, rnx, rbpv, rbnx, rwp, rwn, rwh, rwc, ib, ibd, icg, icgr, ifs, (SystemState.getTcb?_eq_some_iff s1 tid t).mpr ht, e⟩
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
    obtain ⟨tcb, rc, rp, rpv, rnx, rbpv, rbnx, rwp, rwn, rwh, rwc, ib, ibd, icg, icgr, ifs, hL, hTcbEq⟩ :=
      lookupTcb_back_of_objectsAgreeOffSchedulerLinks hRel.objects hL2
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
        exact congrArg KernelObject.tcb (hf tcb rc rp rpv rnx rbpv rbnx rwp rwn rwh rwc ib ibd icg icgr ifs)

/-- SM6.D step congruence: `storeTcbIpcStateAndMessage` succeeds on the
single-core-side state whenever it succeeds on the cross-core-side state,
with off-scheduler-agreeing outputs. -/
theorem storeTcbIpcStateAndMessage_offSchedulerAgrees {s1 s2 r2 : SystemState}
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h2 : storeTcbIpcStateAndMessage s2 tid ipc msg = .ok r2) :
    ∃ r1, storeTcbIpcStateAndMessage s1 tid ipc msg = .ok r1 ∧ OffSchedulerAgrees r1 r2 :=
  modifyTcb_offSchedulerAgrees tid _ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) hRel hInv1 hInv2 h2

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
  modifyTcb_offSchedulerAgrees tid _ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) hRel hInv1 hInv2 h2

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
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) hRel hInv1 hInv2 hM2
  have hInvM1 := modifyTcb_preserves_objects_invExt hInv1 hM1
  have hInvM2 := modifyTcb_preserves_objects_invExt hInv2 hM2
  unfold linkNtfnWaiter storeTcbNtfnLinks
  rw [hM1]
  unfold relinkNtfnNext modifyTcbOpt at hR2 ⊢
  cases tail with
  | none => cases hR2; exact ⟨m1, rfl, hRel1⟩
  | some t => exact modifyTcb_offSchedulerAgrees t _ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) hRel1 hInvM1 hInvM2 hR2

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
        obtain ⟨tcb, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, rfl⟩ :=
          lookupTcb_back_of_objectsAgreeOffSchedulerLinks hRel.objects hL2
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
                obtain ⟨tailTcb, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLT, hTailEq⟩ :=
                  lookupTcb_back_of_objectsAgreeOffSchedulerLinks hRel.objects hLT2
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
states agreeing off the scheduler take the same branch of `cutFrameBelow?` —
it reads `getReply?` and nothing else — and each of the two or three `storeObject`
writes carries the relation. -/
theorem cutReplyFrameStores_offSchedulerAgrees {s1 s2 t1 t2 : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply}
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h1 : cutReplyFrameStores s1 rid above r a = .ok t1)
    (h2 : cutReplyFrameStores s2 rid above r a = .ok t2) :
    OffSchedulerAgrees t1 t2 := by
  have hGR : ∀ q, s2.getReply? q = s1.getReply? q :=
    fun q => hRel.objects.getReply? q
  have hBelow : cutFrameBelow? s2 rid r above = cutFrameBelow? s1 rid r above := by
    unfold cutFrameBelow?
    cases hP : r.prev with
    | none => rfl
    | some below => simp only []; rw [hGR below]
  rcases cutReplyFrameStores_cases h1 with ⟨m1, hB1, hSa1, hSb1⟩ |
    ⟨below, b, m1, n1, hB1, hSa1, hSb1, hSc1⟩
  · rcases cutReplyFrameStores_cases h2 with ⟨m2, _, hSa2, hSb2⟩ |
      ⟨_, _, _, _, hB2, _, _, _⟩
    · exact storeObject_offSchedulerAgrees _ _
        (storeObject_offSchedulerAgrees _ _ hRel hInv1 hInv2 hSa1 hSa2)
        (SeLe4n.Model.storeObject_preserves_objects_invExt s1 m1 _ _ hInv1 hSa1)
        (SeLe4n.Model.storeObject_preserves_objects_invExt s2 m2 _ _ hInv2 hSa2) hSb1 hSb2
    · rw [hBelow, hB1] at hB2; cases hB2
  · rcases cutReplyFrameStores_cases h2 with ⟨_, hB2, _⟩ |
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
read off `getReply?` alone (`cutReplyFrameOutOrSelf_decision`), so agreeing
object stores take the same branch; its writes are `storeObject`s, whose
congruence carries every other field. -/
theorem cutReplyFrameOutOrSelf_offSchedulerAgrees {s1 s2 : SystemState}
    (rid : SeLe4n.ReplyId)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt) :
    OffSchedulerAgrees (cutReplyFrameOutOrSelf s1 rid)
      (cutReplyFrameOutOrSelf s2 rid) := by
  have hGR : ∀ q, s2.getReply? q = s1.getReply? q :=
    fun q => hRel.objects.getReply? q
  rcases cutReplyFrameOutOrSelf_decision s1 rid with
    ⟨r1, above, a, hR1, hN1, hA1, hP1, hS1⟩ |
      ⟨r1, below, b, hR1, hN1, hPv1, hB1, hBn1, hS1⟩ | ⟨hId1, hNo1, hNoS1⟩
  · rcases cutReplyFrameOutOrSelf_decision s2 rid with
      ⟨r2, above', a', hR2, hN2, hA2, _hP2, hS2⟩ |
        ⟨r2, _, _, hR2, hN2, _, _, _, _⟩ | ⟨_, hNo2, _⟩
    · have hRe : r2 = r1 := Option.some.inj (hR2.symm.trans ((hGR rid).trans hR1))
      subst hRe
      have hAb : above = above' := ReplyStackLink.frame.inj (Option.some.inj (hN1.symm.trans hN2))
      subst hAb
      have hAe : a' = a := Option.some.inj (hA2.symm.trans ((hGR above).trans hA1))
      subst hAe
      exact cutReplyFrameStores_offSchedulerAgrees hRel hInv1 hInv2 hS1 hS2
    · have hRe : r2 = r1 := Option.some.inj (hR2.symm.trans ((hGR rid).trans hR1))
      subst hRe; rw [hN1] at hN2; cases hN2
    · exact absurd hP1 (hNo2 r1 above a ((hGR rid).trans hR1) hN1 ((hGR above).trans hA1))
  · rcases cutReplyFrameOutOrSelf_decision s2 rid with
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
  · rcases cutReplyFrameOutOrSelf_decision s2 rid with
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
    (cutReplyFrameOutOrSelf_offSchedulerAgrees rid hRel hInv1 hInv2)
    (cutReplyFrameOutOrSelf_preserves_objects_invExt s1 rid hInv1)
    (cutReplyFrameOutOrSelf_preserves_objects_invExt s2 rid hInv2) h1 h2

/-- WS-ZA ZA6.3: the same off every scheduler link — no release-queue field is a
capability slot. -/
theorem capabilityBadgesWellFormed_of_objectsAgreeOffSchedulerLinks {s1 s2 : SystemState}
    (hA : s2.objectsAgreeOffSchedulerLinks s1) (h : capabilityBadgesWellFormed s1) :
    capabilityBadgesWellFormed s2 :=
  capabilityBadgesWellFormed_of_slotCap_back h fun _ _ hO =>
    let ⟨o, ho, hs, _⟩ := hA.slots_back hO; ⟨o, ho, hs⟩

/-- WS-ZA ZA6.3: `badgeWellFormed` carries off every scheduler link. -/
theorem badgeWellFormed_of_objectsAgreeOffSchedulerLinks {s1 s2 : SystemState}
    (hA : s2.objectsAgreeOffSchedulerLinks s1) (h : badgeWellFormed s1) : badgeWellFormed s2 :=
  ⟨fun oid n b hO hb => h.1 oid n b (hA.get_notification_iff.mp hO) hb,
   capabilityBadgesWellFormed_of_objectsAgreeOffSchedulerLinks hA h.2⟩


/-- WS-ZA ZA5.11: the capability half of `badgeWellFormed` carries across a
word write: no word is a capability slot. -/
theorem capabilityBadgesWellFormed_of_objectsAgreeOffTaint {s1 s2 : SystemState}
    (hA : s1.objectsAgreeOffTaint s2) (h : capabilityBadgesWellFormed s1) :
    capabilityBadgesWellFormed s2 :=
  capabilityBadgesWellFormed_of_slotCap_back h fun oid o' hO =>
    (hA.some_iff oid o' hO).elim fun o ⟨ho, e⟩ => ⟨o, ho, by
      have e' := congrArg KernelObject.slotCap e
      simpa only [KernelObject.eraseTaint, KernelObject.slotCap_withTaintWords] using e'⟩

/-- WS-ZA ZA5.11: **the whole bundle carries across the taint step** — two
states whose stores agree off the taint words satisfy `ipcInvariantFull`
interchangeably (`ipcReadViewAgreement.of_objectsAgreeOffTaint`). -/
theorem ipcInvariantFull_of_objectsAgreeOffTaint {s1 s2 : SystemState}
    (hA : s1.objectsAgreeOffTaint s2) (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ipcInvariantFull_of_readViewAgreement (.of_objectsAgreeOffTaint hA)
    (.of_objectsAgreeOffTaint hA)
    (capabilityBadgesWellFormed_of_objectsAgreeOffTaint hA h.badgeWellFormed.2) h

/-- WS-ZA ZA6.3: `ipcInvariant` reads the notifications alone, which hold no
scheduler link. -/
theorem ipcInvariant_of_objectsAgreeOffSchedulerLinks {st st' : SystemState}
    (hA : st'.objectsAgreeOffSchedulerLinks st) (h : ipcInvariant st) : ipcInvariant st' :=
  fun oid ntfn hL => h oid ntfn (hA.get_notification_iff.mp hL)

/-- WS-ZA ZA6.3: a step writing only scheduler links — run-queue or
release-queue — preserves every thread's binding. -/
theorem sameSchedContextBindings.of_objectsAgreeOffSchedulerLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffSchedulerLinks st) : sameSchedContextBindings st st' := by
  intro tid tcb' hObj
  run_links_back h at tcb' hObj
  exact ⟨tcb', hObj, rfl⟩

/-- WS-ZA ZA6.3: a step writing only scheduler links frames every owner: a
context's release fields are outside its bound thread. -/
theorem donationOwnerFrameExcept.of_objectsAgreeOffSchedulerLinks {st st' : SystemState}
    {woken : SeLe4n.ThreadId} (h : st'.objectsAgreeOffSchedulerLinks st) :
    donationOwnerFrameExcept st st' woken := by
  refine ⟨fun _ _ hSc => (h.get_sc hSc).elim fun sc' hs =>
    ⟨sc', hs.1, SeLe4n.Kernel.SchedContext.proj_eq_of_withoutRelease_eq (·.boundThread) hs.2⟩,
    fun _ tcb hT => ?_⟩
  run_links_fwd h at tcb hT
  exact ⟨_, hT, rfl, Or.inr rfl⟩

/-- WS-ZA ZA6.3: **the whole-bundle transport off every scheduler link** — two
states whose object stores agree off the run-queue and release-queue links
satisfy `ipcInvariantFull` interchangeably: no conjunct reads either queue's
links. -/
theorem ipcInvariantFull_of_objectsAgreeOffSchedulerLinks {s1 s2 : SystemState}
    (hA : s2.objectsAgreeOffSchedulerLinks s1)
    (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ipcInvariantFull_of_readViewAgreement (.of_objectsAgreeOffSchedulerLinks hA)
    (.of_objectsAgreeOffSchedulerLinks hA)
    (capabilityBadgesWellFormed_of_objectsAgreeOffSchedulerLinks hA h.badgeWellFormed.2) h

/-- WS-SM SM6.D, restated for WS-ZA ZA4.5: **the whole-bundle transport** —
two states whose object stores agree off the run-queue links satisfy the
twenty-one conjuncts of `ipcInvariantFull` interchangeably.  This is the lever that carries the single-core whole-bundle
theorems across the cross-core wake, whose run-queue placement differs. -/
theorem ipcInvariantFull_of_objectsAgreeOffRunLinks {s1 s2 : SystemState}
    (hA : s2.objectsAgreeOffRunLinks s1)
    (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ipcInvariantFull_of_objectsAgreeOffSchedulerLinks (.of_runLinks hA) h

/-- WS-ZA ZA6.3: a step writing only scheduler links (run-queue links on
threads, release-queue links on contexts) frames the donation chain: no Reply
changes, and a context's stack head lies off its release fields. -/
theorem donationChainFrame.of_objectsAgreeOffSchedulerLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffSchedulerLinks st) : donationChainFrame st st' := by
  refine ⟨fun oid => ?_, fun oid => ?_, fun oid r' hR hC => ⟨r', h.get_reply_iff.mp hR, hC⟩⟩
  · rcases h.pointwise oid with e | ⟨_, _, ht, ht', _⟩ | ⟨_, _, hs, hs', _⟩
    · rw [e]
    · rw [ht, ht']; rfl
    · rw [hs, hs']; rfl
  · rcases h.pointwise oid with e | ⟨_, _, ht, ht', _⟩ | ⟨sc, sc', hs, hs', e⟩
    · rw [e]
    · rw [ht, ht']; rfl
    · rw [hs, hs']
      have hr := congrArg SchedContext.scReply e
      exact congrArg some hr

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
the scheduler links (WS-ZA ZA4.5 / ZA6.3), exactly as
`ipcInvariantFull_of_objectsAgreeOffSchedulerLinks` does for the full one. -/
theorem ipcInvariantFullExceptDonationOwner_of_objectsAgreeOffSchedulerLinks {s1 s2 : SystemState}
    {woken : SeLe4n.ThreadId}
    (hA : s2.objectsAgreeOffSchedulerLinks s1)
    (h : ipcInvariantFullExceptDonationOwner s1 woken) :
    ipcInvariantFullExceptDonationOwner s2 woken := by
  have hView : ipcReadViewAgreement s1 s2 := .of_objectsAgreeOffSchedulerLinks hA
  exact ⟨ipcInvariant_of_readViewAgreement hView h.1,
   dualQueueSystemInvariant_of_readViewAgreement hView h.2.1,
   allPendingMessagesBounded_of_readViewAgreement hView h.2.2.1,
   badgeWellFormed_of_objectsAgreeOffSchedulerLinks hA h.2.2.2.1,
   blockedThreadsPendingMessageConsistent_of_readViewAgreement hView h.2.2.2.2.1,
   endpointQueueNoDup_of_readViewAgreement hView h.2.2.2.2.2.1,
   ipcStateQueueMembershipConsistent_of_readViewAgreement hView h.2.2.2.2.2.2.1,
   queueNextBlockingConsistent_of_readViewAgreement hView h.2.2.2.2.2.2.2.1,
   queueHeadBlockedConsistent_of_readViewAgreement hView h.2.2.2.2.2.2.2.2.1,
   blockedThreadTimeoutConsistent_of_readViewAgreement hView h.2.2.2.2.2.2.2.2.2.1,
   donationChainAcyclic_of_readViewAgreement hView h.2.2.2.2.2.2.2.2.2.2.1,
   donationOwnerValidExcept_of_readViewAgreement hView h.donationOwnerValidExcept,
   donationBudgetTransfer_of_readViewAgreement hView h.2.2.2.2.2.2.2.2.2.2.2.2.1,
   replyCallerLinkage_of_readViewAgreement hView h.replyCallerLinkage,
   pendingReceiveReplyWellFormed_of_readViewAgreement hView
     h.pendingReceiveReplyWellFormed,
   donationOwnerUnique_of_readViewAgreement hView h.donationOwnerUnique,
   endpointQueueTailBlockedConsistent_of_readViewAgreement hView
     h.endpointQueueTailBlockedConsistent,
   queueNextTargetBlocked_of_readViewAgreement hView h.queueNextTargetBlocked,
   .of_codes (.of_objectsAgreeOffSchedulerLinks hA) h.notificationBindingReciprocal,
   endpointQueueLinksOnlyBlocked_of_readViewAgreement hView h.endpointQueueLinksOnlyBlocked⟩

/-- The transition frame nearly every capability-only dispatch arm induces:
objects untouched.  `ipcInvariantFull` reads nothing else, so it transports
whole. -/
theorem ipcInvariantFull_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects)
    (h : ipcInvariantFull st) : ipcInvariantFull st' :=
  ipcInvariantFull_of_getElem_eq (fun _ => by rw [hObjs])
    h

end SeLe4n.Kernel
