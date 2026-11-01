-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Budget
import SeLe4n.Kernel.SchedContext.ReplenishQueue
import SeLe4n.Kernel.Scheduler.Operations
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate
import SeLe4n.Model.State
import SeLe4n.Kernel.SchedContext.ReleaseLinks

/-! # SchedContext Operations — WS-Z Phase Z5

Capability-controlled operations to bind threads to scheduling contexts,
configure scheduling parameters, and enforce admission control. These
operations make execution a capability-controlled resource.

## Operations:
- `validateSchedContextParams`: Parameter validation for configure
- `collectSchedContexts`: Collect all SchedContexts for admission control
- `schedContextConfigure`: Configure SchedContext parameters with validation
- `schedContextBind`: Bind a thread to a SchedContext (bidirectional)
- `schedContextUnbind`: Unbind a thread from a SchedContext
-/

namespace SeLe4n.Kernel.SchedContextOps

open SeLe4n
open SeLe4n.Kernel.Concurrency (bootCoreId)
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- WS-SM SM8.B: per-core replenish-queue purging
-- ============================================================================

/-- WS-SM SM8.B / WS-ZA ZA6.3: drop `scId`'s replenishment from the release
queue that holds it, read from the context's own link
(`SystemState.releaseRemoveAnywhere`): exact whichever core that is, so neither
a home core to compute nor a sweep over every core is needed (a context whose
bound thread is gone from the store is purged the same way). -/
def purgeReplenishment (st : SystemState) (scId : SchedContextId) : SystemState :=
  st.releaseRemoveAnywhere scId

/-- WS-ZA ZA6.3: the cores whose replenish queue the purge of `scId` writes —
the one its own link names, or none — read from the context alone, so a
footprint locks the queue the purge edits and no other. -/
def purgeReplenishCores (st : SystemState) (scId : SchedContextId) :
    List SeLe4n.Kernel.Concurrency.CoreId :=
  match st.releaseCoreOf scId with
  | some d => [d]
  | none => []

/-! ### Frames

The release queue is **not** one of the six `observableSlotsConfinedToCores`
slots, so the purge is invisible to per-core confinement.  Stated as `@[simp]`
frames on the helper rather than left to unfold at each use site, so the
confinement proofs reason about the purge as a unit and a later change to its
body cannot silently escape them. -/

theorem purgeReplenishment_releaseOnlyWrite (st : SystemState) (scId : SchedContextId) :
    (purgeReplenishment st scId).releaseOnlyWrite st :=
  SystemState.releaseRemoveAnywhere_releaseOnlyWrite st scId

theorem purgeReplenishment_agree (st : SystemState) (scId : SchedContextId) :
    (purgeReplenishment st scId).objectsAgreeOffReleaseLinks st :=
  SystemState.releaseRemoveAnywhere_agree st scId

@[simp] theorem purgeReplenishment_machine (st : SystemState) (scId : SchedContextId) :
    (purgeReplenishment st scId).machine = st.machine :=
  (purgeReplenishment_releaseOnlyWrite st scId).machine

@[simp] theorem purgeReplenishment_tlbShootdown (st : SystemState) (scId : SchedContextId) :
    (purgeReplenishment st scId).tlbShootdown = st.tlbShootdown := by
  rw [(purgeReplenishment_releaseOnlyWrite st scId).1]

@[simp] theorem purgeReplenishment_lifecycle (st : SystemState) (scId : SchedContextId) :
    (purgeReplenishment st scId).lifecycle = st.lifecycle := by
  rw [(purgeReplenishment_releaseOnlyWrite st scId).1]

@[simp] theorem purgeReplenishment_currentOnCore (st : SystemState) (scId : SchedContextId)
    (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishment st scId).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  rw [(purgeReplenishment_releaseOnlyWrite st scId).2]; rfl

@[simp] theorem purgeReplenishment_runQueueOnCore (st : SystemState) (scId : SchedContextId)
    (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishment st scId).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  rw [(purgeReplenishment_releaseOnlyWrite st scId).2]; rfl

@[simp] theorem purgeReplenishment_runQueueEndsOnCore (st : SystemState) (scId : SchedContextId)
    (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishment st scId).scheduler.runQueueEndsOnCore c' =
      st.scheduler.runQueueEndsOnCore c' := by
  rw [(purgeReplenishment_releaseOnlyWrite st scId).2]; rfl

@[simp] theorem purgeReplenishment_activeDomainOnCore (st : SystemState) (scId : SchedContextId)
    (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishment st scId).scheduler.activeDomainOnCore c' =
      st.scheduler.activeDomainOnCore c' := by
  rw [(purgeReplenishment_releaseOnlyWrite st scId).2]; rfl

@[simp] theorem purgeReplenishment_domainTimeRemainingOnCore (st : SystemState)
    (scId : SchedContextId) (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishment st scId).scheduler.domainTimeRemainingOnCore c' =
      st.scheduler.domainTimeRemainingOnCore c' := by
  rw [(purgeReplenishment_releaseOnlyWrite st scId).2]; rfl

@[simp] theorem purgeReplenishment_domainScheduleIndexOnCore (st : SystemState)
    (scId : SchedContextId) (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishment st scId).scheduler.domainScheduleIndexOnCore c' =
      st.scheduler.domainScheduleIndexOnCore c' := by
  rw [(purgeReplenishment_releaseOnlyWrite st scId).2]; rfl

@[simp] theorem purgeReplenishment_reschedulePendingOnCore (st : SystemState)
    (scId : SchedContextId) (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishment st scId).scheduler.reschedulePendingOnCore c' =
      st.scheduler.reschedulePendingOnCore c' := by
  rw [(purgeReplenishment_releaseOnlyWrite st scId).2]; rfl

theorem purgeReplenishment_getTcb? (st : SystemState) (scId : SchedContextId)
    (t : SeLe4n.ThreadId) : (purgeReplenishment st scId).getTcb? t = st.getTcb? t :=
  (purgeReplenishment_agree st scId).getTcb? t

theorem purgeReplenishment_objects_invExt (st : SystemState) (scId : SchedContextId)
    (h : st.objects.invExt) : (purgeReplenishment st scId).objects.invExt :=
  SystemState.releaseRemoveAnywhere_objects_invExt st scId h

/-- **The purge writes the queue of the core the context's own link names, and
no other** — the exactness half of every footprint that names that core. -/
theorem purgeReplenishment_replenishQueueOnCore (st : SystemState)
    (scId : SchedContextId) (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishment st scId).scheduler.replenishQueueOnCore c =
      if st.releaseCoreOf scId = some c then (st.scheduler.replenishQueueOnCore c).remove scId
      else st.scheduler.replenishQueueOnCore c :=
  SystemState.releaseRemoveAnywhere_replenishQueueOnCore st scId c

theorem purgeReplenishment_replenishQueueOnCore_ne (st : SystemState)
    (scId : SchedContextId) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (h : st.releaseCoreOf scId ≠ some c) :
    (purgeReplenishment st scId).scheduler.replenishQueueOnCore c =
      st.scheduler.replenishQueueOnCore c :=
  SystemState.releaseRemoveAnywhere_replenishQueueOnCore_ne st scId c h

/-- **The purge writes exactly the cores its resolver names.** -/
theorem purgeReplenishment_replenishQueueOnCore_of_not_mem (st : SystemState)
    (scId : SchedContextId) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (h : c ∉ purgeReplenishCores st scId) :
    (purgeReplenishment st scId).scheduler.replenishQueueOnCore c =
      st.scheduler.replenishQueueOnCore c := by
  refine purgeReplenishment_replenishQueueOnCore_ne st scId c fun e => h ?_
  unfold purgeReplenishCores; rw [e]; exact List.mem_singleton_self c

/-- **Over agreeing queues the purge drops the context's entries from every
core's queue.** -/
theorem purgeReplenishment_entries {st : SystemState} (hRef : st.releaseQueueRefined)
    (scId : SchedContextId) (c : SeLe4n.Kernel.Concurrency.CoreId) :
    ((purgeReplenishment st scId).scheduler.replenishQueueOnCore c).entries =
      (st.scheduler.replenishQueueOnCore c).entries.filter (fun (id, _) => !(id == scId)) :=
  SystemState.releaseRemoveAnywhere_entries hRef scId c

/-- An entry naming the purged context survives only on a core its own link did
not name. -/
theorem purgeReplenishment_entries_self (st : SystemState)
    (scId : SchedContextId) (c : SeLe4n.Kernel.Concurrency.CoreId) (e : SchedContextId × Nat)
    (he : e ∈ ((purgeReplenishment st scId).scheduler.replenishQueueOnCore c).entries)
    (hs : e.1 = scId) : st.releaseCoreOf scId ≠ some c :=
  SystemState.releaseRemoveAnywhere_entries_self st scId c e he hs

theorem purgeReplenishment_entries_subset (st : SystemState)
    (scId : SchedContextId) (c : SeLe4n.Kernel.Concurrency.CoreId) (e : SchedContextId × Nat)
    (he : e ∈ ((purgeReplenishment st scId).scheduler.replenishQueueOnCore c).entries) :
    e ∈ (st.scheduler.replenishQueueOnCore c).entries :=
  SystemState.releaseRemoveAnywhere_entries_subset st scId c e he

theorem purgeReplenishment_refined {st : SystemState} (h : st.releaseQueueRefined)
    (scId : SchedContextId) : (purgeReplenishment st scId).releaseQueueRefined :=
  SystemState.releaseRemoveAnywhere_refined h scId

/-- The purge is a run-queue frame stage off the purged context: it writes
contexts' release fields and the release queues alone. -/
theorem purgeReplenishment_runQueueFrameStage (st : SystemState) (scId : SchedContextId) :
    SystemState.RunQueueFrameStage (· = scId) st (purgeReplenishment st scId) :=
  .of_releaseOnlyWrite (purgeReplenishment_releaseOnlyWrite st scId)
    (purgeReplenishment_agree st scId) (purgeReplenishment_objects_invExt st scId)
    (fun _ h => purgeReplenishment_refined h scId)
    (fun S hS _ hR h => SystemState.refillsSoundExcept_of_keptOff
      (.of_releaseWrite (purgeReplenishment_agree st scId) fun c e he => by
        rw [purgeReplenishment_entries hR scId c]
        obtain ⟨a, b⟩ := e
        simp only [List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne]
        exact ⟨fun h => h.1, fun h => ⟨h, he⟩⟩)
      hS (purgeReplenishment_refined hR scId) h)

/-- WS-ZA ZA6.4: **purging a context with nothing pending while bound keeps
the refill state sound off every set** — the entries it drops are its own, and
it is not bound and pending, so nothing is stranded; the rest of the queues and
every context's refills are kept. -/
theorem purgeReplenishment_refillsSoundExcept {S : SchedContextId → Prop} {st : SystemState}
    (hR : st.releaseQueueRefined) (scId : SchedContextId)
    (hU : (st.getSchedContext? scId).bind SchedContext.boundReleaseKey? = none)
    (h : st.refillsSoundExcept S) : (purgeReplenishment st scId).refillsSoundExcept S := by
  refine SystemState.refillsSoundExcept_of_releaseMove
    (.of_agreeOffReleaseLinks (purgeReplenishment_agree st scId)) ?_
    (fun c e he => ⟨c, purgeReplenishment_entries_subset st scId c e he⟩)
    (purgeReplenishment_refined hR scId) h
  intro c e _ he
  by_cases hs : e.1 = scId
  · right; rw [hs, hU]; exact fun h => by cases h
  · left
    refine ⟨c, ?_⟩
    rw [purgeReplenishment_entries hR scId c]
    obtain ⟨a, b⟩ := e
    exact List.mem_filter.mpr ⟨he, by simpa using hs⟩

/-- The purge of a context with nothing pending while bound is a run-queue
stage. -/
theorem purgeReplenishment_runQueueStage (st : SystemState) (scId : SchedContextId)
    (hU : (st.getSchedContext? scId).bind SchedContext.boundReleaseKey? = none) :
    SystemState.RunQueueStage st (purgeReplenishment st scId) :=
  .of_releaseOnlyWrite (purgeReplenishment_releaseOnlyWrite st scId)
    (purgeReplenishment_agree st scId) (purgeReplenishment_objects_invExt st scId)
    (fun _ h => purgeReplenishment_refined h scId)
    (fun _ _ hq s => purgeReplenishment_refillsSoundExcept hq scId hU s)

-- ============================================================================
-- Z5-F1: Parameter validation
-- ============================================================================

/-- Maximum priority value (seL4: 255). -/
def maxPriorityVal : Nat := 255

/-- Maximum number of scheduling domains (seL4: 16). -/
def numDomainsVal : Nat := 16

/-- Z5-F1: Validate SchedContext configuration parameters.
Returns error if any parameter violates well-formedness constraints:
- `period > 0` (required for CBS)
- `budget > 0` (AK6-A / SC-H01: zero-budget rejection — a stored
  replenishment with `amount.val = 0` would violate the
  `replenishmentListWellFormed` invariant which forbids zero-amount
  entries; also, a zero-budget SchedContext cannot make progress and
  starves its bound thread)
- `budget ≤ period` (cannot use more than 100% of a period)
- `priority ≤ maxPriority` (within valid priority range)
- `domain < numDomains` (within valid domain range) -/
def validateSchedContextParams (budget period priority _deadline domain : Nat)
    : Except KernelError Unit :=
  if period == 0 then .error .invalidArgument
  else if budget == 0 then .error .invalidArgument
  else if budget > period then .error .invalidArgument
  else if priority > maxPriorityVal then .error .invalidArgument
  else if domain ≥ numDomainsVal then .error .invalidArgument
  else .ok ()

-- ============================================================================
-- Z5-F2: Admission control
-- ============================================================================

/-- Z5-F2: Collect all SchedContext objects from the object store for admission
control, optionally excluding a specific SchedContext (used when reconfiguring
an existing SchedContext to avoid double-counting its bandwidth). -/
def collectSchedContexts (st : SystemState) (excludeId : Option ObjId := none)
    : List SchedContext :=
  -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.  Lift
  -- the raw `ObjId` through `SchedContextId.ofObjId` and route the
  -- variant discrimination through `getSchedContext?`.
  st.objectIndex.filterMap fun oid =>
    if excludeId == some oid then none
    else st.getSchedContext? (SchedContextId.ofObjId oid)

/-- Z5-F2: Check admission control — total bandwidth including candidate
must not exceed 100% (1000 per-mille). When reconfiguring an existing
SchedContext, `excludeId` prevents the old configuration from being
double-counted. -/
def checkAdmission (st : SystemState) (candidate : SchedContext)
    (excludeId : Option ObjId := none) : Bool :=
  admissionCheck (collectSchedContexts st excludeId) candidate

/-- **WS-ZA ZA5.2**: the utilization admission sums, added to `acc`, walking the
object index itself: no list of contexts is collected and no closure is built.
The context `ex` is left out when `hasEx` holds — a reconfiguration's own — as
two plain arguments, so no `Option` is built to carry it. -/
def admissionUtilizationFrom (st : SystemState) (hasEx : Bool) (ex : ObjId) :
    List ObjId → Nat → Nat
  | [], acc => acc
  | oid :: rest, acc =>
    admissionUtilizationFrom st hasEx ex rest
      (if hasEx && ex == oid then acc
       else match st.getSchedContext? (SchedContextId.ofObjId oid) with
         | some sc => acc + sc.utilizationPerMille
         | none => acc)

/-- `admissionUtilizationFrom`'s two plain arguments for an optional exclusion. -/
@[inline] def admissionUtilizationOf (st : SystemState) (excludeId : Option ObjId) : Nat :=
  match excludeId with
  | some e => admissionUtilizationFrom st true e st.objectIndex 0
  | none => admissionUtilizationFrom st false ⟨0⟩ st.objectIndex 0

theorem admissionUtilizationFrom_eq (st : SystemState) (excludeId : Option ObjId)
    (l : List ObjId) (acc : Nat) :
    admissionUtilizationFrom st excludeId.isSome (excludeId.getD ⟨0⟩) l acc =
      (l.filterMap fun oid =>
        if excludeId == some oid then none
        else st.getSchedContext? (SchedContextId.ofObjId oid)).foldl
        (fun acc sc => acc + sc.utilizationPerMille) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons oid rest ih =>
    have hEx : (excludeId.isSome && excludeId.getD ⟨0⟩ == oid) = (excludeId == some oid) := by
      cases excludeId <;> simp
    simp only [admissionUtilizationFrom, ih, List.filterMap_cons, hEx]
    by_cases h : (excludeId == some oid) = true
    · simp only [h, ↓reduceIte]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      cases st.getSchedContext? (SchedContextId.ofObjId oid) <;> rfl

theorem admissionUtilizationOf_eq (st : SystemState) (excludeId : Option ObjId) :
    admissionUtilizationOf st excludeId =
      (collectSchedContexts st excludeId).foldl
        (fun acc sc => acc + sc.utilizationPerMille) 0 := by
  rw [collectSchedContexts, ← admissionUtilizationFrom_eq]
  cases excludeId <;> rfl

/-- **WS-ZA ZA5.2**: the compiled `checkAdmission` — the sum taken over the
object index in place (`admissionUtilizationFrom`), so admitting a
reconfiguration builds nothing. -/
@[inline] def checkAdmissionImpl (st : SystemState) (candidate : SchedContext)
    (excludeId : Option ObjId := none) : Bool :=
  admissionUtilizationOf st excludeId + candidate.utilizationPerMille ≤ 1000

@[csimp] theorem checkAdmission_eq_impl : @checkAdmission = @checkAdmissionImpl := by
  funext st candidate excludeId
  simp only [checkAdmission, checkAdmissionImpl, admissionCheck, admissionUtilizationOf_eq]

-- ============================================================================
-- Z5-F3: schedContextConfigure
-- ============================================================================

/-- WS-OD (v0.35.3): may a reconfiguration of SchedContext `scId` propagate its
**thread-owned** parameters — base priority and domain — into `boundTcb`?

Exactly when `boundTcb` **owns** that reservation.  One predicate for both
halves of `schedContextConfigureBoundPropagate`, so they provably gate on the
same fact: a domain gate that asked the question a second way would be the
"one question, two answers" shape `CLAUDE.md` forbids, and the two halves
disagreeing is how half a fix reads as a whole one. -/
def schedContextConfigurePropagates (boundTcb : TCB)
    (scId : SeLe4n.SchedContextId) : Prop :=
  boundTcb.schedContextBinding.ownScId? = some scId

instance (boundTcb : TCB) (scId : SeLe4n.SchedContextId) :
    Decidable (schedContextConfigurePropagates boundTcb scId) := by
  unfold schedContextConfigurePropagates; infer_instance

/-- A donee's thread-owned parameters are never propagated to: it owns no
reservation, so no reconfiguration of the one it runs on reaches its TCB. -/
@[simp] theorem schedContextConfigurePropagates_donated (boundTcb : TCB)
    {scId held : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    (h : boundTcb.schedContextBinding = .donated held owner) :
    ¬ schedContextConfigurePropagates boundTcb scId := by
  simp [schedContextConfigurePropagates, h]

/-- A thread that owns the reconfigured reservation is propagated to — the
`.bound` case, so neither half of the propagation is dead code. -/
@[simp] theorem schedContextConfigurePropagates_bound (boundTcb : TCB)
    {scId : SeLe4n.SchedContextId}
    (h : boundTcb.schedContextBinding = .bound scId) :
    schedContextConfigurePropagates boundTcb scId := by
  simp [schedContextConfigurePropagates, h]

/-- The bound-thread propagation tail of `schedContextConfigure`, factored so
the invariant surface can speak about it by name: rewrite the bound TCB's
priority (when it moved), re-bucket the thread on its home core (when queued),
then align its domain (when it moved) — **all of it gated on
`schedContextConfigurePropagates`**, one predicate over
`SchedContextBinding.ownScId?` that both halves consult.

**WS-OD (v0.35.3) — the mirror authority crossing.**  `sc.boundThread` is the
thread the reservation is *charged to*, which after a donation is the **donee**,
not the owner: `donateSchedContext` writes `boundThread := some serverTid`.
Propagating a reconfiguration there unconditionally let a caller holding a
capability on the **client's** reservation rewrite the **server's** own
`TCB.priority` *and* `TCB.domain` — the mirror of the crossing
`updatePrioritySource` had, and permanent, since the donee keeps both fields
after the donation returns.  Neither is the caller's to set: `.tcbSetPriority`
answers to a TCB-write right over the target plus an MCP ceiling, and the domain
is the partition the thread runs in.

Both halves are propagations of the **thread-owned** parameters onto the
reservation the thread owns — the AK2-B convention — and the invariants they
maintain (`boundThreadPriorityConsistent`, `boundThreadDomainConsistent`) are
both `.bound`-only, so gating on ownership is the exact relation rather than a
weakening: it fires on every state those invariants constrain.  `scId?` would be
the wrong classifier here, and the wrong one is what the crossing was.  Both
halves consult the **one** predicate, so a later cut cannot gate one and not the
other.

Budget, period and deadline are **reservation-owned** and are written by
`schedContextConfigure` itself, on the SchedContext, where a donee reads them
at every depth.  A reconfiguration therefore still retunes the donee's budget
and deadline, which is correct: that is the reservation the caller holds. -/
def schedContextConfigureBoundPropagate (stStored : SystemState)
    (scId : SeLe4n.SchedContextId)
    (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (hBound : stStored.getTcb? boundTid = some boundTcb)
    (priority domain : Nat) : SystemState :=
  let stProp : SystemState :=
    if boundTcb.priority.val = priority ∨
       ¬ schedContextConfigurePropagates boundTcb scId then
      stStored
    else
      let newPri : SeLe4n.Priority := ⟨priority⟩
      let boundTcb2 : TCB := { boundTcb with priority := newPri }
      -- The bound TCB is handed in, so the write is the typed in-place rewrite
      -- under the store's witness for it (`v0.35.71`): `schedContextConfigure`
      -- resolves the thread once, through the witnessed lookup, and passes the
      -- proof down rather than looking the record up a second time.
      let stWithTcb : SystemState :=
        stStored.rewriteObject boundTid.toObjId (KernelObject.tcb boundTcb2)
          (SystemState.rewriteAdmissible_tcb hBound boundTcb2)
      -- The bucket the thread now belongs in, read off the record that is
      -- being stored: `TCB.boostedPriority` (`Model/Object/Types.lean`) is the
      -- one answer the run queue is keyed by, and taking it from `boundTcb2`
      -- rather than re-deriving it from `priority` is what stops the stored
      -- priority and the bucket from being computed by two expressions.
      let effectivePri : SeLe4n.Priority := boundTcb2.boostedPriority
      let boundHome := determineTargetCore stWithTcb boundTid
      -- The thread leaves its bucket and rejoins the new one through its TCB
      -- run-queue links (WS-ZA ZA4.5).
      if stWithTcb.queuedOn boundHome boundTid then
        stWithTcb.runRequeueOnCore boundHome boundTid effectivePri
      else stWithTcb
  -- The domain half reads the record the priority half may have rewritten, so
  -- it resolves the thread again -- through the witnessed lookup, whose
  -- witness is its own rewrite's proof -- and writes only when the domain
  -- moved: the `if` stays outside the rewrite so an unchanged domain is no
  -- write at all, as before.
  match stProp.getTcbWitnessed? boundTid with
  | some ⟨currentTcb, hCurrent⟩ =>
    if currentTcb.domain.val = domain ∨
       ¬ schedContextConfigurePropagates boundTcb scId then stProp
    else
      let newDom : SeLe4n.DomainId := ⟨domain⟩
      let currentTcb2 : TCB := { currentTcb with domain := newDom }
      stProp.rewriteObject boundTid.toObjId (KernelObject.tcb currentTcb2)
        (SystemState.rewriteAdmissible_tcb hCurrent currentTcb2)
  | none => stProp

/-- The propagation tail keeps the object store's invariant: its two writes are
TCB rewrites, and the re-bucket writes only run-queue links and the scheduler.  The chain re-walk
`schedContextConfigure` runs after it needs this. -/
theorem schedContextConfigureBoundPropagate_preserves_objects_invExt (stStored : SystemState)
    (scId : SeLe4n.SchedContextId) (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (hBound : stStored.getTcb? boundTid = some boundTcb) (priority domain : Nat)
    (hInv : stStored.objects.invExt) :
    (schedContextConfigureBoundPropagate stStored scId boundTid boundTcb hBound priority
      domain).objects.invExt := by
  unfold schedContextConfigureBoundPropagate
  have hProp : ∀ s : SystemState, s.objects.invExt →
      ∀ (hW : ∀ t, s.getTcbWitnessed? boundTid = some t → True),
      (match s.getTcbWitnessed? boundTid with
        | some ⟨currentTcb, hCurrent⟩ =>
          if currentTcb.domain.val = domain ∨
             ¬ schedContextConfigurePropagates boundTcb scId then s
          else
            s.rewriteObject boundTid.toObjId (KernelObject.tcb { currentTcb with domain := ⟨domain⟩ })
              (SystemState.rewriteAdmissible_tcb hCurrent { currentTcb with domain := ⟨domain⟩ })
        | none => s).objects.invExt := by
    intro s hs _
    split
    · split
      · exact hs
      · exact SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hs
    · exact hs
  apply hProp _ _ (fun _ _ => trivial)
  split
  · exact hInv
  · dsimp only []
    have hW := SystemState.rewriteObject_preserves_objects_invExt stStored boundTid.toObjId
      (KernelObject.tcb { boundTcb with priority := ⟨priority⟩ })
      (SystemState.rewriteAdmissible_tcb hBound _) hInv
    split
    · exact SystemState.runRequeueOnCore_objects_invExt _ _ _ _ hW
    · exact hW

/-- **WS-ZA ZA6.4**: whether a configure keeps the context's head refill
(seL4-MCS's `refill_update`) rather than starting its refills afresh
(`refill_new`): exactly when the context is in use — configured before, its
bound thread runnable — and the new parameters are not round robin (budget equal
to period), as `invokeSchedControl_ConfigureFlags` chooses.  A context in use is
spending its head, so a configure that refilled it would hand it budget it has
already used. -/
@[inline] def configureKeepsHead (st : SystemState) (sc : SchedContext) (budget period : Nat) :
    Bool :=
  budget != period && sc.budget.val != 0 &&
    match sc.boundThread with
    | some t => (st.getTcb? t).any TCB.isRunnable
    | none => false

/-- **WS-ZA ZA5.2**: the context `schedContextConfigure` stores, as a function of
the stored one, so the store can rewrite it in its slot.  WS-ZA ZA6.4: its refills
are seL4-MCS's: the head kept and trimmed to the new budget, the rest of the
budget one new period on (`SchedContext.refillUpdate`), when `keep`
(`configureKeepsHead`); otherwise the whole budget in one refill released at
`timer` (`SchedContext.refillNew`).  Either way the refills hold the new budget
exactly once (`refillUpdate_refillTotal`, `refillNew_refillTotal`).  The context
is left off every release queue; the configure then places it. -/
@[inline] def configuredSchedContext (budget period priority deadline domain timer : Nat)
    (keep : Bool) (sc : SchedContext) : SchedContext :=
  let base : SchedContext :=
    { sc with
      budget := ⟨budget⟩
      period := ⟨period⟩
      priority := ⟨priority⟩
      deadline := ⟨deadline⟩
      domain := ⟨domain⟩
      releaseNextCode := 0
      releaseCoreCode := 0
      releaseAt := 0 }
  if keep then base.refillUpdate budget period timer else base.refillNew budget timer

/-- `configuredSchedContext`'s fresh branch (`refill_new`), out of line: its
updates then reuse the context's cell when the store holds the only reference,
where inlined into the branch on `keep` they sit in a join point that drops the
reuse and allocates the context and its object on every configure. -/
@[noinline] def configuredSchedContextFresh (budget period priority deadline domain timer : Nat)
    (sc : SchedContext) : SchedContext :=
  let base : SchedContext :=
    { sc with
      budget := ⟨budget⟩
      period := ⟨period⟩
      priority := ⟨priority⟩
      deadline := ⟨deadline⟩
      domain := ⟨domain⟩
      releaseNextCode := 0
      releaseCoreCode := 0
      releaseAt := 0 }
  base.refillNew budget timer

/-- `configuredSchedContext`'s kept-head branch (`refill_update`), out of line. -/
@[noinline] def configuredSchedContextKept (budget period priority deadline domain timer : Nat)
    (sc : SchedContext) : SchedContext :=
  let base : SchedContext :=
    { sc with
      budget := ⟨budget⟩
      period := ⟨period⟩
      priority := ⟨priority⟩
      deadline := ⟨deadline⟩
      domain := ⟨domain⟩
      releaseNextCode := 0
      releaseCoreCode := 0
      releaseAt := 0 }
  base.refillUpdate budget period timer

/-- The compiled `configuredSchedContext`: the branch on `keep` first, each
branch's updates out of line. -/
@[inline] def configuredSchedContextImpl (budget period priority deadline domain timer : Nat)
    (keep : Bool) (sc : SchedContext) : SchedContext :=
  if keep then configuredSchedContextKept budget period priority deadline domain timer sc
  else configuredSchedContextFresh budget period priority deadline domain timer sc

/-- The compiled configured context is the configured context. -/
@[csimp] theorem configuredSchedContext_eq_impl :
    @configuredSchedContext = @configuredSchedContextImpl := by
  funext budget period priority deadline domain timer keep sc
  unfold configuredSchedContext configuredSchedContextImpl configuredSchedContextKept
    configuredSchedContextFresh
  cases keep <;> rfl

/-- WS-ZA ZA6.6: the configure keeps the context's end of the yield link. -/
@[simp] theorem configuredSchedContext_yieldFromCode (budget period priority deadline domain
    timer : Nat) (keep : Bool) (sc : SchedContext) :
    (configuredSchedContext budget period priority deadline domain timer keep sc).yieldFromCode =
      sc.yieldFromCode := by
  unfold configuredSchedContext; cases keep <;> simp

/-- The configured context reads nothing of the stored one's release fields. -/
theorem configuredSchedContext_withoutRelease (budget period priority deadline domain timer : Nat)
    (keep : Bool) (sc : SchedContext) :
    configuredSchedContext budget period priority deadline domain timer keep sc.withoutRelease =
      configuredSchedContext budget period priority deadline domain timer keep sc := rfl

/-- The configured context holds the new budget and period. -/
theorem configuredSchedContext_budget_period (budget period priority deadline domain timer : Nat)
    (keep : Bool) (sc : SchedContext) :
    (configuredSchedContext budget period priority deadline domain timer keep sc).budget =
        ⟨budget⟩ ∧
      (configuredSchedContext budget period priority deadline domain timer keep sc).period =
        ⟨period⟩ := by
  unfold configuredSchedContext
  split
  · obtain ⟨-, hb, hp, -⟩ := SchedContext.fields_of_refillsErased
      (SchedContext.refillUpdate_refillsErased _ budget period timer)
    exact ⟨hb, hp⟩
  · exact ⟨rfl, rfl⟩

/-- The configured context keeps the stored one's binding, reply stack and loan
origin: a configure writes parameters and refills only. -/
theorem configuredSchedContext_binding (budget period priority deadline domain timer : Nat)
    (keep : Bool) (sc : SchedContext) :
    (configuredSchedContext budget period priority deadline domain timer keep sc).boundThreadCode =
        sc.boundThreadCode ∧
      (configuredSchedContext budget period priority deadline domain timer keep sc).scReply =
        sc.scReply ∧
      (configuredSchedContext budget period priority deadline domain timer keep sc).donationOrigin =
        sc.donationOrigin := by
  unfold configuredSchedContext
  split
  · obtain ⟨-, -, -, -, -, -, hb, hr, hd, -⟩ := SchedContext.fields_of_refillsErased
      (SchedContext.refillUpdate_refillsErased _ budget period timer)
    exact ⟨hb, hr, hd⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- The configured context is linked on no release queue: the configure then
places it. -/
@[simp] theorem configuredSchedContext_releaseCoreCode
    (budget period priority deadline domain timer : Nat) (keep : Bool) (sc : SchedContext) :
    (configuredSchedContext budget period priority deadline domain timer keep sc).releaseCoreCode =
      0 := by
  unfold configuredSchedContext
  split
  · exact (SchedContext.fields_of_refillsErased
      (SchedContext.refillUpdate_refillsErased _ budget period timer)).2.2.2.2.2.2.2.2.2.2.1
  · rfl

theorem configuredSchedContext_boundThread (budget period priority deadline domain timer : Nat)
    (keep : Bool) (sc : SchedContext) :
    (configuredSchedContext budget period priority deadline domain timer keep sc).boundThread =
      sc.boundThread := by
  unfold SchedContext.boundThread
  rw [(configuredSchedContext_binding budget period priority deadline domain timer keep sc).1]


/-- **WS-RR RR8.12 Cut B2 (`v0.35.182`)**: a thread a bind must PLACE.

seL4-MCS's `schedContext_bindTCB` ends in
`if (isSchedulable(tcb)) { SCHED_ENQUEUE(tcb); rescheduleRequired(); }`
(read at `13.0.0`); this kernel's bind re-bucketed only a thread already on a
run queue, so a runnable thread that sat on **none** stayed off every queue with
a reservation it could not spend.  `chooseThreadOnCore` selects exclusively from
`runQueueOnCore` and never scans ready TCBs, so that is permanent.

Reachable, and not hypothetically: WS-RR RR8.12 Cut B1 (`v0.35.158`) parks the
holder a donation reclaim unbinds — `.ready`, `.unbound`, on no core — precisely
so it stops running on nobody's budget, and names *"its own manager recovers it …
or a `schedContextBind` once that arm places a parked thread"* as the recovery.
That recovery was closed.  This predicate is what opens it.

Four conjuncts, and each excludes a thread a bind must **not** place:

* `placedCoreOf? st tid = none` — a thread already queued is re-bucketed by the
  step below, and one that is **current** on some core is running, so enqueuing
  it would put it in a run queue and on a processor at once
  (`queueCurrentConsistent`);
* `tcb.ipcState = .ready` — a thread blocked in IPC is owed a wake by whatever
  it is blocked on, and the bind explicitly supports binding a blocked thread
  (Z5-G1's own note).  Placing one would make it selectable while its rendezvous
  is outstanding, which is `queueHeadBlockedConsistent`'s negation;
* `tcb.threadState ≠ .Inactive` — a suspended thread is recovered by
  `.tcbResume`, which demands exactly that flag, so a bind that placed one would
  resurrect a thread its own manager suspended;
* `sc.budgetRemaining.isPositive` — the reservation being bound can run the
  thread **now** (PR #900 review, `v0.36.1`).  This is the selector's own reading:
  for a bound thread `hasSufficientBudget` is exactly `budgetRemaining.isPositive`
  of its reservation (`bindPlacesParkedThread_budget_eq_hasSufficientBudget`), so
  a thread this guard admits is one `chooseBestRunnableEffective` does not skip
  for budget.  Without it, binding an **exhausted** reservation — reachable by
  unbinding one mid-period, which preserves `budgetRemaining = 0` and purges its
  replenishment entry — placed the thread on a run queue it could never be chosen
  from, with no refill ever due to change that, and the bind reported success.
  seL4-MCS refuses the same placement: `schedContext_bindTCB` runs
  `schedContext_resume`, which **postpones** a thread whose head refill is not
  ready and sufficient into the release queue, and `isSchedulable` is false of a
  thread in the release queue, so the `SCHED_ENQUEUE` above does not fire (read at
  `13.0.0`).  WS-ZA ZA6.4: the bind postpones the same way — the reservation
  the guard reads is the one the bind stores, its head released by now
  (`SchedContext.releaseReadyHead`), and a head not yet released puts the
  context on its thread's home core's release queue (`SystemState.releasePlace`),
  so the thread left parked here is woken by the drain at its refill.

The third conjunct reads the **stored** flag and deliberately not
`inferThreadState`, which answers `.Inactive` for *any* thread that is unplaced
and not blocked — which a parked thread is by definition, so the inferred reading
would refuse exactly the shape this guard exists to admit.  The stored flag is
what `.tcbSuspend` writes and `.tcbResume` reads, so it means *"its manager
suspended it"*, and the reclaim's park leaves it alone: measured at `.Ready` on
the live parked holder (`tests/SmpCancellationSuite.lean` §3.26b).

Stated as a definition rather than inline because the footprint, the step and
the witness all have to ask the *same* question, and because a conjunct added to
it must reach every asker. -/
def bindPlacesParkedThread (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (sc : SchedContext) : Bool :=
  !isIdleThreadId tid && (placedCoreOf? st tid).isNone && tcb.isRunnable
    && sc.budgetRemaining.isPositive

/-- **WS-ZA ZA6.4: configure's resume tail**, seL4-MCS's `schedContext_resume`
then `possibleSwitchTo` at the end of `invokeSchedControl_ConfigureFlags`, on the
configured context `sc` and its bound thread `t`, homed on `home`
(`determineTargetCore`):

* a thread `home` queues stays queued while the context can run it now
  (`budgetRemaining` positive), and is taken off its run queue otherwise: seL4
  dequeues it before the refills are rewritten and `schedContext_resume`
  postpones a context whose head refill is not ready, and a postponed thread is
  not schedulable;
* a runnable thread on no queue and no core (`bindPlacesParkedThread`, the
  guard the bind's own enqueue reads) is placed on `home`'s run queue, and
  `home` is flagged to reschedule (`possibleSwitchTo`);
* a thread current on `home` whose context can no longer run it flags `home`
  to reschedule (`rescheduleRequired`);
* anything else is left as it is.

The context's own release queue placement is the configure's (`releasePlace`),
made before this tail, so a context left unready is on `home`'s release queue,
and the drain wakes its thread at its refill. -/
def configureResumeBound (st : SystemState) (t : SeLe4n.ThreadId) (sc : SchedContext) :
    SystemState :=
  let home := determineTargetCore st t
  if st.queuedOn home t then
    if sc.budgetRemaining.isPositive then st else st.runRemoveOnCore home t
  else
    match st.getTcb? t with
    | some tcb =>
      if bindPlacesParkedThread st t tcb sc then
        (st.runEnqueueOnCore home t (resolveInsertPriority st t sc)).markReschedulePendingOnCore home
      else if st.scheduler.currentOnCore home == some t && !sc.budgetRemaining.isPositive then
        st.markReschedulePendingOnCore home
      else st
    | none => st

/-- The resume tail writes the run-queue links alone of the object store. -/
theorem configureResumeBound_objectsAgreeOffRunLinks (st : SystemState)
    (t : SeLe4n.ThreadId) (sc : SchedContext) :
    (configureResumeBound st t sc).objectsAgreeOffRunLinks st := by
  unfold configureResumeBound
  dsimp only
  split
  · split
    · exact .refl _
    · exact SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ _ _
  · split
    · split
      · exact (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _).congr rfl rfl
      · split
        · exact .refl _
        · exact .refl _
    · exact .refl _

theorem configureResumeBound_objects_invExt (st : SystemState)
    (t : SeLe4n.ThreadId) (sc : SchedContext)
    (h : st.objects.invExt) : (configureResumeBound st t sc).objects.invExt := by
  unfold configureResumeBound
  dsimp only
  split
  · split
    · exact h
    · exact SystemState.runRemoveOnCore_objects_invExt _ _ _ h
  · split
    · split
      · exact SystemState.runEnqueueOnCore_objects_invExt _ _ _ _ h
      · split <;> exact h
    · exact h

/-- The resume tail writes no replenish queue. -/
theorem configureResumeBound_replenishQueueOnCore (st : SystemState)
    (t : SeLe4n.ThreadId) (sc : SchedContext) (c : Concurrency.CoreId) :
    (configureResumeBound st t sc).scheduler.replenishQueueOnCore c =
      st.scheduler.replenishQueueOnCore c := by
  unfold configureResumeBound
  dsimp only
  repeat' split
  all_goals simp [SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
    SchedulerState.setRunQueueEndsOnCore_replenishQueueOnCore]

/-- Z5-F3: Configure a SchedContext's scheduling parameters.

1. Validates parameters (period > 0, budget ≤ period, etc.)
2. Checks admission control (total bandwidth ≤ 100%)
3. Clears any stale entries in the system replenish queue for this scId
4. Updates the SchedContext object in the store

AK2-G (S-M05): Any pending replenishment entries previously enqueued for this
SchedContext reference the PRIOR budget/period and therefore become stale the
moment the configure operation rewrites those fields. Without explicit removal,
`processReplenishmentsDue` could re-enqueue the bound thread at the old
replenishment window, violating CBS isolation. The `replenishQueue.remove`
call is idempotent and preserves sort order.

**WS-AL AL8 (cascades AK7-E) — Type-level validity discipline**: the
`scId` parameter has type `ValidObjId`. The Lean type system forbids any
caller from feeding `ObjId.sentinel` into this handler. -/
def schedContextConfigure (vScId : ValidObjId) (budget period priority deadline domain : Nat)
    : Kernel Unit :=
  fun st =>
    match validateSchedContextParams budget period priority deadline domain with
    | .error e => .error e
    | .ok () =>
      -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration. The
      -- original `_ => .error .objectNotFound` arm collapsed wrong-variant
      -- and absent into the same error code, so migration is
      -- semantics-preserving.
      match st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
      | some sc =>
        -- WS-ZA ZA6.4: the refills are seL4-MCS's: a context in use (configured
        -- before, its bound thread runnable, not round robin) keeps its head
        -- (`refill_update`), so a reconfigure cannot hand it budget it has
        -- spent; any other takes the budget in one refill released now
        -- (`refill_new`).  The refills hold the budget once either way.
        let updated : SchedContext :=
          configuredSchedContext budget period priority deadline domain st.machine.timer
            (configureKeepsHead st sc budget period) sc
        if checkAdmission st updated (some vScId.val) then
          -- AK2-G: purge stale system replenishQueue entries for this vScId.val
          -- before storing the reconfigured object.
          let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
          -- WS-SM SM8.B / WS-ZA ZA6.3: purge on the core whose queue holds the
          -- entry, read from the context's own link.  A purge keyed on a core
          -- computed elsewhere misses an entry left on another core, which then
          -- still fires: two budgets in the first period.
          let stCleaned := purgeReplenishment st scIdTyped
          -- AK2-B option B (S-H04): if the SchedContext is currently bound to a
          -- thread and configure changes the SC priority, propagate the new
          -- priority into the bound TCB's `priority` field AND re-bucket the
          -- thread in the RunQueue if present (so `schedulerPriorityMatch`'s
          -- `threadPriority[tid]? = tcb.boostedPriority` continues to
          -- hold under the new TCB priority). Without the RunQueue migration
          -- the thread would remain in the old priority bucket while
          -- `tcb.priority` was updated — a latent priority-inversion vector.
          -- We preserve any existing `pipBoost` by re-inserting at
          -- `max(new priority, pipBoost)`, matching `migrateRunQueueBucket`
          -- in `PriorityManagement.lean`.
          match storeObject vScId.val (KernelObject.schedContext updated) stCleaned with
          | .error e => .error e
          | .ok ((), stStored0) =>
            match sc.boundThread with
            | none => .ok ((), stStored0)
            | some boundTid =>
              -- WS-ZA ZA6.4: a bound context whose head is not yet released
              -- waits on its thread's home core's release queue (seL4-MCS's
              -- `schedContext_resume` postponing it), so its refill is not
              -- stranded: the release queue is what wakes the thread.
              let stStored := stStored0.releasePlace (determineTargetCore st boundTid) scIdTyped

              -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration;
              -- witnessed since `v0.35.71`, so the propagation writes the record
              -- under the store's proof for it.
              match stStored.getTcbWitnessed? boundTid with
              | some ⟨boundTcb, hBound⟩ =>
                -- The reschedule-SGI accumulator (KSC-1): the bound thread's
                -- effective key read against the PRE-state's reservation (the
                -- SC store above moved its deadline and the propagation may
                -- move its priority); `markKeyChangeFor` flags its placement
                -- exactly when the key the selector orders by changed, so an
                -- immaterial reconfigure flags nothing.
                --
                -- A bound thread reply-blocked on a server lends that server its
                -- priority, so a priority propagated here re-walks the server's
                -- inheritance chain (`repropagateFromWaiter`); the boost it held
                -- was computed from the old priority.  The walk runs as the bound
                -- thread's home core, the core this configure's footprint locks.
                --
                -- The reset refills `budgetRemaining`, so a bound thread that had
                -- exhausted its budget becomes one the chooser may pick: a
                -- candidacy gain on the cores queueing it, flagged beside the
                -- key change (`markCandidacyGainFor`, read against the PRE-state's
                -- budget like the key).
                --
                -- WS-ZA ZA6.4: then seL4-MCS's resume tail
                -- (`configureResumeBound`): a thread the configured context can
                -- run now is placed, one it cannot is taken off its queue.
                let preKey := effectiveSchedParams st boundTcb
                .ok ((), configureResumeBound (PriorityInheritance.repropagateFromWaiter
                  (markKeyChangeFor (markCandidacyGainFor
                    (schedContextConfigureBoundPropagate stStored scIdTyped
                      boundTid boundTcb hBound priority domain) boundTid
                    (hasSufficientBudget st boundTcb)) boundTid preKey) boundTid
                  (determineTargetCore st boundTid) st.objectIndex.length)
                  boundTid updated)
              | none => .ok ((), stStored)  -- bound thread's TCB missing: leave as-is
        else
          .error .resourceExhausted
      | none => .error .objectNotFound


/-- **WS-ZA ZA5.2**: `schedContextConfigure`'s checks, read before any write:
the parameters, the context, admission (`checkAdmission` of the configured
context, which reads only its budget and period) and a store that changes only
the object table.  When they pass the configure's state is
`schedContextConfigurePerform` (`schedContextConfigure_of_admitted`). -/
@[inline] def schedContextConfigureAdmitted (st : SystemState) (vScId : ValidObjId)
    (budget period priority deadline domain : Nat) : Bool :=
  match validateSchedContextParams budget period priority deadline domain with
  | .error _ => false
  | .ok () =>
    match st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
    | none => false
    | some _ =>
      decide (admissionUtilizationFrom st true vScId.val st.objectIndex 0 +
          (Bandwidth.mk budget period).utilization ≤ 1000) &&
        storeLeavesIndexAndTypes st vScId.val .schedContext

/-- **WS-ZA ZA5.2**: `schedContextConfigure`'s writes: the replenishment purge,
the context rewritten in its slot (`updateSchedContext`), and, for a bound
context, its placement on its thread's home core's release queue (WS-ZA ZA6.4)
and the specification's propagation over the stored state. -/
@[inline] def schedContextConfigurePerform (st : SystemState) (vScId : ValidObjId)
    (budget period priority deadline domain : Nat) : SystemState :=
  match st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | none => st
  | some sc =>
    let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
    let keep := configureKeepsHead st sc budget period
    let stCleaned := purgeReplenishment st scIdTyped
    let stStored0 := stCleaned.updateSchedContext (SchedContextId.ofObjId vScId.val)
      (configuredSchedContext budget period priority deadline domain st.machine.timer keep)
    match sc.boundThread with
    | none => stStored0
    | some boundTid =>
      let stStored := stStored0.releasePlace (determineTargetCore st boundTid) scIdTyped
      match stStored.getTcbWitnessed? boundTid with
      | some ⟨boundTcb, hBound⟩ =>
        configureResumeBound (PriorityInheritance.repropagateFromWaiter
          (markKeyChangeFor (markCandidacyGainFor
            (schedContextConfigureBoundPropagate stStored scIdTyped
              boundTid boundTcb hBound priority domain) boundTid
            (hasSufficientBudget st boundTcb)) boundTid
            (effectiveSchedParams st boundTcb)) boundTid
          (determineTargetCore st boundTid) st.objectIndex.length)
          boundTid
          (configuredSchedContext budget period priority deadline domain st.machine.timer keep sc)
      | none => stStored

/-- **WS-ZA ZA5.2**: the compiled `schedContextConfigurePerform`.  The bound
thread is cased on before the store, so a context with no bound thread is
rewritten with nothing else holding the entry's state or the context: the
store writes the object table and the context in their slots instead of
copying both (the specification's later `match` keeps `st` and `sc` alive
across it). -/
@[inline] def schedContextConfigurePerformImpl (st : SystemState) (vScId : ValidObjId)
    (budget period priority deadline domain : Nat) : SystemState :=
  match st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | none => st
  | some sc =>
    let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
    match sc.boundThread with
    | none =>
      let timer := st.machine.timer
      (purgeReplenishment st scIdTyped).updateSchedContext
        (SchedContextId.ofObjId vScId.val)
        (configuredSchedContext budget period priority deadline domain timer false)
    | some boundTid =>
      let keep := configureKeepsHead st sc budget period
      let home := determineTargetCore st boundTid
      let stCleaned := purgeReplenishment st scIdTyped
      let stStored0 := stCleaned.updateSchedContext (SchedContextId.ofObjId vScId.val)
        (configuredSchedContext budget period priority deadline domain st.machine.timer keep)
      let stStored := stStored0.releasePlace home scIdTyped
      match stStored.getTcbWitnessed? boundTid with
      | some ⟨boundTcb, hBound⟩ =>
        configureResumeBound (PriorityInheritance.repropagateFromWaiter
          (markKeyChangeFor (markCandidacyGainFor
            (schedContextConfigureBoundPropagate stStored scIdTyped
              boundTid boundTcb hBound priority domain) boundTid
            (hasSufficientBudget st boundTcb)) boundTid
            (effectiveSchedParams st boundTcb)) boundTid
          (determineTargetCore st boundTid) st.objectIndex.length)
          boundTid
          (configuredSchedContext budget period priority deadline domain st.machine.timer keep sc)
      | none => stStored

@[csimp] theorem schedContextConfigurePerform_eq_impl :
    @schedContextConfigurePerform = @schedContextConfigurePerformImpl := by
  funext st vScId budget period priority deadline domain
  unfold schedContextConfigurePerform schedContextConfigurePerformImpl
  cases st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | none => rfl
  | some sc =>
    dsimp only
    cases hB : sc.boundThread with
    | none =>
      have hK : configureKeepsHead st sc budget period = false := by
        unfold configureKeepsHead; rw [hB]; simp
      rw [hK]
    | some b =>
      dsimp only


/-- **WS-ZA ZA5.2**: an admitted configure succeeds, and its state is the
perform's. -/
theorem schedContextConfigure_of_admitted (st : SystemState) (vScId : ValidObjId)
    (budget period priority deadline domain : Nat)
    (h : schedContextConfigureAdmitted st vScId budget period priority deadline domain = true) :
    schedContextConfigure vScId budget period priority deadline domain st =
      .ok ((), schedContextConfigurePerform st vScId budget period priority deadline domain) := by
  unfold schedContextConfigureAdmitted at h
  unfold schedContextConfigure schedContextConfigurePerform
  cases hV : validateSchedContextParams budget period priority deadline domain with
  | error e => simp [hV] at h
  | ok u =>
    cases u
    cases hS : st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
    | none => simp [hV, hS] at h
    | some sc =>
      simp only [hV, hS, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hAdm, hLeaves⟩ := h
      have hCheck : checkAdmission st
          (configuredSchedContext budget period priority deadline domain st.machine.timer
            (configureKeepsHead st sc budget period) sc)
          (some vScId.val) = true := by
        rw [checkAdmission_eq_impl]
        have hb := configuredSchedContext_budget_period budget period priority deadline domain
          st.machine.timer (configureKeepsHead st sc budget period) sc
        simp only [checkAdmissionImpl, admissionUtilizationOf, SchedContext.utilizationPerMille,
          SchedContext.bandwidth, hb.1, hb.2, decide_eq_true_eq]
        simpa using hAdm
      dsimp only
      rw [if_pos hCheck]
      have hW := purgeReplenishment_releaseOnlyWrite st ⟨vScId.val.toNat⟩
      have hA := purgeReplenishment_agree st ⟨vScId.val.toNat⟩
      generalize purgeReplenishment st ⟨vScId.val.toNat⟩ = stC at hW hA
      have hLeavesC : storeLeavesIndexAndTypes stC vScId.val
          (KernelObject.schedContext (configuredSchedContext budget period priority deadline
            domain st.machine.timer (configureKeepsHead st sc budget period) sc)).objectType
            = true := by
        rw [SystemState.releaseOnlyWrite.storeLeavesIndexAndTypes_eq hW hA]
        simpa [KernelObject.objectType] using hLeaves
      rw [storeObject_eq_of_leaves hLeavesC]
      have hSC' := hA.getSchedContext? (SchedContextId.ofObjId vScId.val)
      rw [hS] at hSC'
      cases hSC : stC.getSchedContext? (SchedContextId.ofObjId vScId.val) with
      | none => rw [hSC] at hSC'; cases hSC'
      | some sc' =>
      rw [hSC] at hSC'
      simp only [Option.map_some, Option.some.injEq] at hSC'
      have hEq : ∀ k, configuredSchedContext budget period priority deadline domain
          st.machine.timer k sc'
          = configuredSchedContext budget period priority deadline domain st.machine.timer k sc := by
        intro k
        rw [← configuredSchedContext_withoutRelease, hSC', configuredSchedContext_withoutRelease]
      rw [SystemState.updateSchedContext_eq_of_some hSC
        (configuredSchedContext budget period priority deadline domain st.machine.timer _),
        SeLe4n.SchedContextId.toObjId_ofObjId, hEq]
      cases sc.boundThread with
      | none => rfl
      | some boundTid =>
        simp only []
        split <;> rfl

-- ============================================================================
-- Z5-G1/G2/G3: schedContextBind
-- ============================================================================

-- **Tombstone (`v0.35.157`)**: `replyFrameOnLiveStack` — the bind guard's
-- "is this thread's reply frame on a live stack" test — lives in
-- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` beside `replyFrameHeadContext?`,
-- whose reciprocity check is its `.head` arm.  It moved when the reply pop's
-- origin redirect started asking the same question (`donationOriginRebindable`
-- is `¬ replyFrameOnLiveStack` at the origin): one question, one answer, and
-- the endpoint operations cannot import this module.  `schedContextBind` below
-- reads it under its unqualified name through `open SeLe4n.Kernel`.


/-- A thread the bind places is no idle thread: an idle thread is never queued. -/
theorem bindPlacesParkedThread_not_idle {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} {sc : SchedContext} (h : bindPlacesParkedThread st tid tcb sc = true) :
    isIdleThreadId tid = false := by
  unfold bindPlacesParkedThread at h
  cases hI : isIdleThreadId tid
  · rfl
  · rw [hI] at h; cases h

/-- **Cut B2**: a thread already placed is not placed again — the re-bucket arm's
subject, and the conjunct that keeps a running thread off a run queue. -/
@[simp] theorem bindPlacesParkedThread_of_placed (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (sc : SchedContext) (c : Concurrency.CoreId)
    (h : placedCoreOf? st tid = some c) :
    bindPlacesParkedThread st tid tcb sc = false := by
  unfold bindPlacesParkedThread
  rw [h]
  simp

/-- **Cut B2**: nor is a thread blocked in IPC. -/
@[simp] theorem bindPlacesParkedThread_of_blocked (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (sc : SchedContext) (h : tcb.ipcState ≠ .ready) :
    bindPlacesParkedThread st tid tcb sc = false := by
  unfold bindPlacesParkedThread
  simp [h, TCB.isRunnable]

/-- **Cut B2**: nor a suspended one. -/
@[simp] theorem bindPlacesParkedThread_of_inactive (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (sc : SchedContext) (h : tcb.threadState = SeLe4n.Model.ThreadState.Inactive) :
    bindPlacesParkedThread st tid tcb sc = false := by
  unfold bindPlacesParkedThread
  simp [h, TCB.isRunnable]

/-- **PR #900 review (`v0.36.1`)**: nor a thread whose reservation has no budget
left — it would sit on a run queue the selector skips it on, with nothing due to
refill it. -/
@[simp] theorem bindPlacesParkedThread_of_exhausted (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (sc : SchedContext) (h : sc.budgetRemaining.isPositive = false) :
    bindPlacesParkedThread st tid tcb sc = false := by
  unfold bindPlacesParkedThread
  simp [h]

/-- **The budget conjunct IS the selector's question.**  For a thread bound to a
reservation the store holds, `hasSufficientBudget` answers exactly
`budgetRemaining.isPositive` of that reservation — so the guard and
`chooseBestRunnableEffective`'s budget filter cannot disagree about which thread
a bind may place; a Tier 3 anchor pins the conjunct's spelling in the guard. -/
theorem bindPlacesParkedThread_budget_eq_hasSufficientBudget (st : SystemState) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hBind : tcb.schedContextBinding = .bound scId) (hSc : st.getSchedContext? scId = some sc) :
    hasSufficientBudget st tcb = sc.budgetRemaining.isPositive := by
  simp [hasSufficientBudget, hBind, hSc]

/-- **Cut B2**: the guard reads only the SCHEDULER, two fields of the TCB it is
handed and the budget of the reservation it is handed, so it is insensitive to
the bind's own object writes.

Which is what lets the transition evaluate it at its intermediate state and a
caller check it at the pre-state: the bind rewrites a SchedContext and the
thread's `schedContextBinding` / `priority`, and none of the four conjuncts reads
any of them.  The fourth reads `sc` — the record the bind resolved before either
write, an *argument* rather than a store lookup — and the bind's own rewrite of
that SchedContext changes `boundThread` and `donationOrigin`, never
`budgetRemaining`. -/
theorem bindPlacesParkedThread_congr {st st' : SystemState} (tid : SeLe4n.ThreadId)
    (tcb : TCB) (sc : SchedContext) (h : st'.scheduler = st.scheduler)
    (hQ : SystemState.RunCoresAgree st' st) :
    bindPlacesParkedThread st' tid tcb sc = bindPlacesParkedThread st tid tcb sc := by
  unfold bindPlacesParkedThread placedCoreOf?
  have hF : (fun c => st'.queuedOn c tid || st'.scheduler.currentOnCore c == some tid) =
      (fun c => st.queuedOn c tid || st.scheduler.currentOnCore c == some tid) := by
    funext c; rw [hQ.queuedOn, h]
  rw [hF]

/-- Z5-G1/G2/G3: Bind a thread to a SchedContext.
1. Precondition: SchedContext has no bound thread, TCB is unbound
2. Set bidirectional binding (sc.boundThread, tcb.schedContextBinding)
3. Write both updated objects to store
4. If thread is in RunQueue, remove and re-insert at the propagated priority
   so the recorded bucket tracks the TCB field step 2 just wrote
   (`effectiveParamsMatchRunQueue`, which since `v0.35.133` reads that field
   at every binding rather than the reservation's)

**WS-AL AL8 (cascades AK7-E)**: `scId` is `ValidObjId`, `threadId` is
`ValidThreadId` for compile-time sentinel rejection on BOTH IDs. -/
def schedContextBind (vScId : ValidObjId) (vThreadId : ValidThreadId) : Kernel Unit :=
  fun st =>
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration. Both
    -- the original `_ => .error .objectNotFound` arms collapsed
    -- wrong-variant and absent into the same error code, so migrating to
    -- `none => .error .objectNotFound` is semantics-preserving.
    match st.getSchedContextWitnessed? (SchedContextId.ofObjId vScId.val) with
    | some ⟨sc, hSc⟩ =>
      -- Z5-G1: Precondition check — SchedContext must not already have a bound thread
      if sc.boundThread.isSome then .error .illegalState
      -- WS-OD (`v0.35.4`): a context that heads a reply stack is on loan down a
      -- call chain and owed back along it; binding it elsewhere would give it a
      -- second claimant the pop then displaces.  Refused until the chain unwinds
      -- (or its callers are cancelled, which reclaims it).
      else if sc.scReply.isSome then .error .illegalState
      else
        match st.getTcb? vThreadId.val with
        | some tcb =>
          -- AE3-A/U-11: Domain consistency check — reject cross-domain binding.
          -- The domain filter (chooseBestRunnableInDomainEffective) uses tcb.domain
          -- but effective priority resolves from sc.domain. Mismatched domains would
          -- cause a thread to pass the domain filter by TCB domain but be prioritized
          -- by SchedContext domain.
          if tcb.domain != sc.domain then .error .invalidArgument
          -- WS-OD (`v0.35.4`): a thread blocked on a reply whose frame is on a
          -- live stack (`next.isSome`) is owed a context by the pop that reaches
          -- that frame, and the pop writes its binding; giving it a second
          -- context now would be overwritten by that pop, orphaning this one.
          -- Refused while the frame is on a stack; a frame with no upward link
          -- (`next = none`), or one below a severed cut whose link nothing
          -- answers, is owed nothing, and binding is allowed.
          else if replyFrameOnLiveStack st tcb then .error .illegalState
          else
          -- Z5-G1: Precondition check — TCB must be unbound.
          -- AI6-D (L-13): `schedContextBind` checks `tcb.schedContextBinding`
          -- (binding state: `.unbound`) but NOT the thread's operational state
          -- (`ipcState`, scheduler state). This matches seL4 MCS semantics
          -- where SchedContext binding is independent of thread execution
          -- state — binding can occur while a thread is blocked, ready, or in
          -- any other operational state. Operational safety is ensured by the
          -- SchedContext invariant bundle (Invariant/Defs.lean), not by
          -- per-bind state checks.
          match tcb.schedContextBinding with
          | .unbound =>
            -- Z5-G2: Bidirectional binding
            -- AK2-B option B (S-H04): Propagate SC priority to TCB priority.
            -- This establishes `tcb.priority = sc.priority` at bind time.
            -- Matches seL4 MCS, where bind transfers scheduling authority from
            -- the TCB to its bound SchedContext.
            --
            -- **WS-RR (`v0.35.133`): do not read this write as redundant.**  Its
            -- original justification was that `schedulerPriorityMatch` and
            -- `effectiveParamsMatchRunQueue` jointly forced `tcb.priority =
            -- sc.priority` in the extended bundle with no operation establishing
            -- it.  That is no longer true: with `TCB.priority` the base's one
            -- home neither predicate reads a reservation, so the pair forces
            -- nothing here.  What the write is for now is the thing it always
            -- *did* — it is how a reservation configures its bound thread's
            -- band, it is what `boundThreadPriorityConsistent` states, and with
            -- the field the only home the scheduler reads, deleting it would
            -- make `schedContextBind` silently not apply the band it is being
            -- asked to apply.
            let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
            -- **WS-HP HP10.4: a bind ends any loan, so the origin clears.**  The
            -- thread now *owns* this reservation, which is the state the origin
            -- records a departure from — so a recorded origin here is residue, and
            -- leaving it would let a later pop hand the reservation to a thread
            -- this bind has nothing to do with.  Defense in depth rather than a
            -- reachable repair: the guard above already refuses a context that
            -- heads a reply stack, and the pop's bottom arm clears the field when
            -- a chain unwinds — but "no state reaches this" is an argument about
            -- every path into the operation, and clearing costs one field write.
            --
            -- WS-ZA ZA6.4: a head refill released by now is made the head
            -- (`releaseReadyHead`), as seL4-MCS's `schedContext_resume` finds the
            -- head ready; one not yet released leaves the context postponed on
            -- its thread's home core's release queue (the placement below).
            let scR := sc.releaseReadyHead st.machine.timer
            let updatedSc := { scR with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val),
                                        donationOrigin := none }
            -- Write both updated objects (`v0.35.71`): the SchedContext under the
            -- witness its own lookup carries, then the TCB through the typed
            -- rewrite over the rewritten state -- its lookup is re-resolved
            -- there, because a witness taken at `st` does not carry across a
            -- rewrite without `invExt`, which executable code has no proof of.
            -- The record it writes is the stored one with its binding and
            -- priority moved: exactly what the raw insert wrote from `tcb`.
            let st1 := st.rewriteObject vScId.val (KernelObject.schedContext updatedSc)
              (SystemState.rewriteAdmissible_schedContext hSc updatedSc)
            let st2 := st1.updateTcb vThreadId.val fun t =>
              { t with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (SchedContextBinding.bound scIdTyped), scBindingOwnerCode := 0,
                       priority := sc.priority }
            -- Z5-G3: If thread is in RunQueue, remove and re-insert at
            -- SchedContext-derived priority. Under dequeue-on-dispatch, only
            -- runnable-but-not-current threads are in the RunQueue. After bind,
            -- the effective priority resolves from the SchedContext, so we must
            -- update the RunQueue entry to match.
            -- AE3-J/SC-09: Run queue insertion uses pre-update sc.priority.
            -- AG1-A: Now uses effective priority (base + PIP boost) to ensure
            -- PIP-boosted threads are placed in the correct bucket.
            -- WS-SM SM8.B (review round 13): the bound thread's HOME core, not the
            -- boot core — see `schedContextConfigure` above for the defect this fixes.
            --
            -- **WS-RR RR8.12 Cut B2 (`v0.35.182`): a bind PLACES a parked
            -- runnable thread**, which is seL4-MCS's `SCHED_ENQUEUE` tail and
            -- which this kernel did not do.  The `else` arm below used to be
            -- `st2` unconditionally, so a runnable thread on no run queue —
            -- exactly what Cut B1's reclaim parks — kept a reservation it could
            -- never spend: `chooseThreadOnCore` selects only from
            -- `runQueueOnCore`.  `bindPlacesParkedThread` is the guard, and its
            -- four conjuncts are why placing is safe here (see its docstring):
            -- the fourth (PR #900 review, `v0.36.1`) is the reservation's own
            -- budget, so a bind never places a thread the selector would then
            -- skip forever.  The insert priority is `resolveInsertPriority`, the
            -- SAME one the re-bucket arm uses, so the two arms cannot disagree
            -- about which bucket a bound thread belongs in.
            let bindHome := determineTargetCore st2 vThreadId.val
            -- Both arms move the thread through its TCB run-queue links
            -- (WS-ZA ZA4.5).
            let st3 := if st2.queuedOn bindHome vThreadId.val then
              st2.runRequeueOnCore bindHome vThreadId.val (resolveInsertPriority st2 vThreadId.val sc)
            else if bindPlacesParkedThread st2 vThreadId.val tcb scR then
              -- The reschedule-SGI accumulator (KSC-1): the placement is a
              -- wake on `bindHome` (the diff's queue rule), flagged as such.
              (st2.runEnqueueOnCore bindHome vThreadId.val
                (resolveInsertPriority st2 vThreadId.val sc)).markReschedulePendingOnCore bindHome
            else st2
            -- The reschedule-SGI accumulator (KSC-1): the bind moved the
            -- thread's effective key (its deadline is the reservation's now,
            -- its priority the reservation's); the hook flags a re-bucketed
            -- or current thread's core exactly when that key changed.
            --
            -- WS-ZA ZA6.4: then the context waits on the home core's release
            -- queue for a head not yet released (seL4-MCS's `postpone`), so a
            -- thread bound to an exhausted context is woken by its refill.
            .ok ((), (markKeyChangeFor st3 vThreadId.val (effectiveSchedParams st tcb)).releasePlace
              bindHome scIdTyped)
          | _ => .error .illegalState
        | none => .error .objectNotFound
    | none => .error .objectNotFound

/-- **WS-ZA ZA5.2**: `schedContextBind`'s checks, read before anything is
written: the context is stored, binds no thread and heads no reply stack; the
thread is stored, shares the context's domain, is owed no context by a live
reply stack, and is unbound.  When they pass the operation's state is
`schedContextBindPerform` (`schedContextBind_of_admitted`), so the routed arm
writes the context and the thread in place instead of holding the pre-state for
a refusal that cannot come. -/
@[inline] def schedContextBindAdmitted (st : SystemState) (vScId : ValidObjId)
    (vThreadId : ValidThreadId) : Bool :=
  match st.getSchedContextWitnessed? (SchedContextId.ofObjId vScId.val) with
  | none => false
  | some ⟨sc, _⟩ =>
    if sc.boundThread.isSome then false
    else if sc.scReply.isSome then false
    else
      match st.getTcb? vThreadId.val with
      | none => false
      | some tcb =>
        if tcb.domain != sc.domain then false
        else if replyFrameOnLiveStack st tcb then false
        else
          match tcb.schedContextBinding with
          | .unbound => true
          | _ => false

/-- **WS-ZA ZA5.2**: `schedContextBind`'s writes, the operation's success arm
written out over the same lookups: the context names the thread, the thread is
bound at the context's priority, the run-queue stage re-keys or places it on its
home core, and the key hook flags the cores whose decision the move stales. -/
@[inline] def schedContextBindPerform (st : SystemState) (vScId : ValidObjId)
    (vThreadId : ValidThreadId) : SystemState :=
  match st.getSchedContextWitnessed? (SchedContextId.ofObjId vScId.val) with
  | none => st
  | some ⟨sc, hSc⟩ =>
    match st.getTcb? vThreadId.val with
    | none => st
    | some tcb =>
      let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
      let scR := sc.releaseReadyHead st.machine.timer
      let updatedSc := { scR with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val),
                                  donationOrigin := none }
      let st1 := st.rewriteObject vScId.val (KernelObject.schedContext updatedSc)
        (SystemState.rewriteAdmissible_schedContext hSc updatedSc)
      let st2 := st1.updateTcb vThreadId.val fun t =>
        { t with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (SchedContextBinding.bound scIdTyped), scBindingOwnerCode := 0,
                 priority := sc.priority }
      let bindHome := determineTargetCore st2 vThreadId.val
      let st3 := if st2.queuedOn bindHome vThreadId.val then
        st2.runRequeueOnCore bindHome vThreadId.val (resolveInsertPriority st2 vThreadId.val sc)
      else if bindPlacesParkedThread st2 vThreadId.val tcb scR then
        (st2.runEnqueueOnCore bindHome vThreadId.val
          (resolveInsertPriority st2 vThreadId.val sc)).markReschedulePendingOnCore bindHome
      else st2
      (markKeyChangeFor st3 vThreadId.val (effectiveSchedParams st tcb)).releasePlace bindHome
        scIdTyped

/-- **WS-ZA ZA5.2**: an admitted bind succeeds, and its state is the perform's. -/
theorem schedContextBind_of_admitted (st : SystemState) (vScId : ValidObjId)
    (vThreadId : ValidThreadId) (h : schedContextBindAdmitted st vScId vThreadId = true) :
    schedContextBind vScId vThreadId st = .ok ((), schedContextBindPerform st vScId vThreadId) := by
  unfold schedContextBindAdmitted at h
  unfold schedContextBind schedContextBindPerform
  cases hW : st.getSchedContextWitnessed? (SchedContextId.ofObjId vScId.val) with
  | none => simp [hW] at h
  | some w =>
    obtain ⟨sc, hSc⟩ := w
    simp only [hW] at h ⊢
    by_cases hB : sc.boundThread.isSome = true
    · simp [hB] at h
    by_cases hR : sc.scReply.isSome = true
    · simp [hB, hR] at h
    simp only [hB, hR, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hT : st.getTcb? vThreadId.val with
    | none => simp [hT] at h
    | some tcb =>
      simp only [hT] at h ⊢
      by_cases hD : (tcb.domain != sc.domain) = true
      · simp [hD] at h
      by_cases hL : replyFrameOnLiveStack st tcb = true
      · simp [hD, hL] at h
      simp only [hD, hL, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hBind : tcb.schedContextBinding with
      | unbound => rfl
      | bound _ => simp [hBind] at h
      | donated _ _ => simp [hBind] at h

/-- **WS-ZA ZA5.2**: the compiled `schedContextBindPerform`.  Every read of the
pre-state — the context's priority and budget, the thread's runnability and its
old key as three parts — is made before the first write, so neither the state,
the context nor the TCB is held across a write and each is written in its slot
(`updateSchedContext`, `updateTcb`); the placement reads the written state only
(`schedContextBindPerform_eq_impl`). -/
@[inline] def schedContextBindPerformImpl (st : SystemState) (vScId : ValidObjId)
    (vThreadId : ValidThreadId) : SystemState :=
  match st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | none => st
  | some sc =>
    match st.getTcb? vThreadId.val with
    | none => st
    | some tcb =>
      let now := st.machine.timer
      let scPrio := sc.priority
      -- The released head's budget, read off the fields when nothing is due
      -- (the release then writes nothing, `releaseReadyHead_of_not_due`).
      let scFunded := if sc.releaseDue now then (sc.releaseReadyHead now).budgetRemaining.isPositive
        else sc.budgetRemaining.isPositive
      let runnable := tcb.isRunnable
      let p0 := tcb.boostedPriority
      let d0 := effectiveDeadline st tcb
      let dom0 := tcb.domain
      let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
      let st1 := st.updateSchedContext (SchedContextId.ofObjId vScId.val) fun s =>
        { s.releaseReadyHead now with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val),
                                      donationOrigin := none }
      let st2 := st1.updateTcb vThreadId.val fun t =>
        { t with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (SchedContextBinding.bound scIdTyped), scBindingOwnerCode := 0,
                 priority := scPrio }
      let bindHome := determineTargetCore st2 vThreadId.val
      -- The insertion band, `resolveInsertPriority`'s, as the boosted priority
      -- every arm of the resolver yields
      -- (`resolveEffectivePrioDeadline_fst_eq_boostedPriority`): the resolver's
      -- pair, and the closure its fallback is shared through, are never built.
      let insertPrio : SeLe4n.Priority := match st2.getTcb? vThreadId.val with
        | some t => t.boostedPriority
        | none => scPrio
      let st3 := if st2.queuedOn bindHome vThreadId.val then
        st2.runRequeueOnCore bindHome vThreadId.val insertPrio
      else if !isIdleThreadId vThreadId.val && (placedCoreOf? st2 vThreadId.val).isNone &&
          runnable && scFunded then
        (st2.runEnqueueOnCore bindHome vThreadId.val insertPrio).markReschedulePendingOnCore bindHome
      else st2
      (markKeyChangeParts st3 vThreadId.val p0 d0 dom0).releasePlace bindHome scIdTyped

@[csimp] theorem schedContextBindPerform_eq_impl :
    @schedContextBindPerform = @schedContextBindPerformImpl := by
  funext st vScId vThreadId
  unfold schedContextBindPerform schedContextBindPerformImpl
  have hVal := SystemState.getSchedContextWitnessed?_val st (SchedContextId.ofObjId vScId.val)
  rcases hW : st.getSchedContextWitnessed? (SchedContextId.ofObjId vScId.val) with _ | ⟨sc, hS⟩
  · rw [hW] at hVal
    simp only [Option.map_none] at hVal
    simp only [← hVal]
  · simp only [hS]
    cases hT : st.getTcb? vThreadId.val with
    | none => rfl
    | some tcb =>
      dsimp only
      rw [SystemState.updateSchedContext_eq_of_some hS, markKeyChangeFor_eq_parts,
        effectiveSchedParams_eq_parts]
      simp only [resolveInsertPriority, resolveEffectivePrioDeadline_fst_eq_boostedPriority]
      have hF : (if sc.releaseDue st.machine.timer then
            (sc.releaseReadyHead st.machine.timer).budgetRemaining.isPositive
          else sc.budgetRemaining.isPositive) =
          (sc.releaseReadyHead st.machine.timer).budgetRemaining.isPositive := by
        split
        · rfl
        · rename_i hd; rw [SchedContext.releaseReadyHead_of_not_due _ _ (by simpa using hd)]
      rw [hF]
      rfl

-- ============================================================================
-- Z5-H1/H2/H3: schedContextUnbind
-- ============================================================================

/-- WS-ZA ZA4.5: the unbind's run-queue stage on the thread's home core — a
queued thread is re-keyed at its legacy priority, a thread that was current is
placed there (a wake, flagged), and any other is left where it is.  Both moves go
through the thread's TCB run-queue links. -/
def schedContextUnbindQueueStage (st0 : SystemState) (home : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool) : SystemState :=
  if st0.queuedOn home tid then st0.runRequeueOnCore home tid prio
  else if wasCurrent then (st0.runEnqueueOnCore home tid prio).markReschedulePendingOnCore home
  else st0

/-- The unbind's run-queue stage writes objects only in run-queue links. -/
theorem schedContextUnbindQueueStage_objectsAgreeOffRunLinks (st0 : SystemState)
    (home : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool) :
    (schedContextUnbindQueueStage st0 home tid prio wasCurrent).objectsAgreeOffRunLinks st0 := by
  unfold schedContextUnbindQueueStage
  split
  · exact SystemState.runRequeueOnCore_objectsAgreeOffRunLinks _ _ _ _
  · split
    · exact SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _
    · exact SystemState.objectsAgreeOffRunLinks.refl _

/-- The unbind's run-queue stage keeps the object store's invariant. -/
theorem schedContextUnbindQueueStage_objects_invExt (st0 : SystemState)
    (home : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool)
    (hInv : st0.objects.invExt) :
    (schedContextUnbindQueueStage st0 home tid prio wasCurrent).objects.invExt := by
  unfold schedContextUnbindQueueStage
  split
  · exact SystemState.runRequeueOnCore_objects_invExt _ _ _ _ hInv
  · split
    · exact SystemState.runEnqueueOnCore_objects_invExt _ _ _ _ hInv
    · exact hInv

/-- The unbind's run-queue stage writes no replenish queue. -/
@[simp] theorem schedContextUnbindQueueStage_replenishQueueOnCore (st0 : SystemState)
    (home : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool)
    (c : Concurrency.CoreId) :
    (schedContextUnbindQueueStage st0 home tid prio wasCurrent).scheduler.replenishQueueOnCore c =
      st0.scheduler.replenishQueueOnCore c := by
  unfold schedContextUnbindQueueStage
  split
  · simp
  · split
    · simp [SystemState.markReschedulePendingOnCore]
    · rfl

/-! The unbind's run-queue stage writes only its home core's queue and flag:
every other observable per-core slot comes through unchanged. -/
@[simp] theorem schedContextUnbindQueueStage_machine (st0 : SystemState)
    (home : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool) :
    (schedContextUnbindQueueStage st0 home tid prio wasCurrent).machine = st0.machine := by
  unfold schedContextUnbindQueueStage
  split
  · simp
  · split
    · simp [SystemState.markReschedulePendingOnCore]
    · rfl

@[simp] theorem schedContextUnbindQueueStage_currentOnCore (st0 : SystemState)
    (home : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool)
    (c : Concurrency.CoreId) :
    (schedContextUnbindQueueStage st0 home tid prio wasCurrent).scheduler.currentOnCore c =
      st0.scheduler.currentOnCore c := by
  unfold schedContextUnbindQueueStage
  split
  · simp
  · split
    · simp [SystemState.markReschedulePendingOnCore]
    · rfl

@[simp] theorem schedContextUnbindQueueStage_activeDomainOnCore (st0 : SystemState)
    (home : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool)
    (c : Concurrency.CoreId) :
    (schedContextUnbindQueueStage st0 home tid prio wasCurrent).scheduler.activeDomainOnCore c =
      st0.scheduler.activeDomainOnCore c := by
  unfold schedContextUnbindQueueStage
  split
  · simp
  · split
    · simp [SystemState.markReschedulePendingOnCore]
    · rfl

@[simp] theorem schedContextUnbindQueueStage_domainTimeRemainingOnCore (st0 : SystemState)
    (home : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool)
    (c : Concurrency.CoreId) :
    (schedContextUnbindQueueStage st0 home tid prio wasCurrent).scheduler.domainTimeRemainingOnCore c =
      st0.scheduler.domainTimeRemainingOnCore c := by
  unfold schedContextUnbindQueueStage
  split
  · simp
  · split
    · simp [SystemState.markReschedulePendingOnCore]
    · rfl

@[simp] theorem schedContextUnbindQueueStage_domainScheduleIndexOnCore (st0 : SystemState)
    (home : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool)
    (c : Concurrency.CoreId) :
    (schedContextUnbindQueueStage st0 home tid prio wasCurrent).scheduler.domainScheduleIndexOnCore c =
      st0.scheduler.domainScheduleIndexOnCore c := by
  unfold schedContextUnbindQueueStage
  split
  · simp
  · split
    · simp [SystemState.markReschedulePendingOnCore]
    · rfl

@[simp] theorem schedContextUnbindQueueStage_runQueueOnCore_ne (st0 : SystemState)
    (home : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool)
    (c : Concurrency.CoreId) (hne : home ≠ c) :
    (schedContextUnbindQueueStage st0 home tid prio wasCurrent).scheduler.runQueueOnCore c =
      st0.scheduler.runQueueOnCore c := by
  unfold schedContextUnbindQueueStage
  split
  · simp [hne]
  · split
    · simp [SystemState.markReschedulePendingOnCore,
        SystemState.runEnqueueOnCore_runQueueOnCore_ne _ _ _ _ _ hne]
    · rfl

/-- Z5-H1/H2/H3: Unbind a thread from a SchedContext.
1. Verify the SchedContext has a bound thread
2. (H1) If the bound thread is **running on some core**, clear that core's
   current slot to trigger rescheduling — the core is found by
   `runningCoreOf?`, not by `determineTargetCore`: the two agree on committed
   states only through the placement invariant (WS-ZA ZA6.3; before it an
   unbound-affinity thread could run on a secondary core, PR #861 review
   rounds 39/40), and the wrapper's scheduling point reads the former
3. (H2) Re-bucket the thread on its **home** core at its post-unbind legacy
   TCB priority — removed and re-inserted if it was queued, inserted if it was
   current, in **this** transition
4. Clear both sides of the bidirectional binding
5. (H3) Remove SchedContext from replenish queue

**The re-bucket is immediate, not deferred** (PR #861 review rounds 38/40).
This step used to remove the thread and say "it will be re-enqueued at legacy
TCB priority by the next schedule call if still runnable".  Nothing does:
`chooseThreadOnCore` selects exclusively from `runQueueOnCore` and never scans
ready TCBs, and an unbound thread is fully schedulable (the `.unbound` arm of
`resolveEffectivePrioDeadline` returns the legacy TCB priority rather than
making the thread passive).  A successful unbind therefore left a runnable
thread ready and permanently unschedulable.  Callers and proof authors should
not reason about an intermediate non-runnable state: there is none.

**WS-AL AL8 (cascades AK7-E)**: `scId` is `ValidObjId` for compile-time
sentinel rejection. -/
def schedContextUnbind (vScId : ValidObjId) : Kernel Unit :=
  fun st =>
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration. The
    -- original `_ => .error .objectNotFound` arm collapsed wrong-variant
    -- and absent into the same error code, so migration is
    -- semantics-preserving.
    match st.getSchedContextWitnessed? (SchedContextId.ofObjId vScId.val) with
    | some ⟨sc, hSc⟩ =>
      match sc.boundThread with
      | none => .error .illegalState
      | some tid =>
        match st.getTcb? tid with
        | some tcb =>
          -- WS-OD (`v0.35.4`): a holder that received the context by donation
          -- is not unbound here.  The donation pop is keyed on the recorded
          -- server's `.donated` binding; erasing that binding while the
          -- context's stack still names the caller left the caller's frame
          -- dead on the stack when the server later replied (the Reply and the
          -- context could never be retyped again).  The context's owner
          -- reclaims it by cancelling the blocked caller, which returns it and
          -- unbinds the holder.  (seL4 allows the unbind and re-donates at the
          -- pop because its pop is keyed on the reply object; this kernel keys
          -- the pop on the binding and refuses the unbind instead — fail closed.)
          if tcb.schedContextBinding.isDonated then .error .illegalState else
          -- Z5-H1: Preemption guard — if the bound thread is current, clear
          -- current to force rescheduling.  Under dequeue-on-dispatch the
          -- current thread is not in the RunQueue, so clearing current is
          -- sufficient to take it off the processor.
          --
          -- WS-SM SM8.B (review round 13): keyed on `bootCoreId` the guard never
          -- fired for a thread current on a secondary core, which kept running
          -- at its now-revoked SC priority.
          --
          -- WS-SM SM8.B (review round 39): …and keying it on the *home* core was
          -- still wrong, because the guard and the scheduling point that follows
          -- it were reading **different cores**.  `schedContextUnbindOnCore`
          -- resolves its reschedule target through `runningCoreOf?` — the core
          -- actually executing the thread — while this guard used
          -- `determineTargetCore`, the affinity home.  Those agree on every
          -- committed state under the placement invariant (`currentHome`,
          -- WS-ZA ZA6.3); before it they diverged for an **unbound-affinity
          -- thread running on a secondary core**.  In that case home was boot,
          -- `wasCurrent` was false, and the thread was left current on the
          -- secondary core AND absent from every run queue — the round-13
          -- defect surviving one field over.  Both halves read `runningCoreOf?`,
          -- the core whose slot the guard clears.
          --
          -- The *queue* side below stays on the home core, and deliberately: an
          -- unbound thread belongs on its home core's run queue, which is where
          -- the next selection will look for it.
          let unbindHome := determineTargetCore st tid
          let runCore? := runningCoreOf? st tid
          let wasCurrent := runCore?.isSome
          -- The reschedule-SGI accumulator (KSC-1): clearing a core's
          -- `current` slot stales its decision (the diff's slot rule).
          let sched0 := match runCore? with
            | some runCore => (st.scheduler.setCurrentOnCore runCore none)
                |>.markReschedulePendingOnCore runCore
            | none => st.scheduler
          -- Z5-H2: re-bucket the thread at its post-unbind (legacy) priority.
          --
          -- WS-SM SM8.B (PR #861 review round 14): this used to **remove** the
          -- thread and rely on "the next schedule call will re-enqueue it
          -- correctly if still runnable".  Nothing does.  `chooseThreadOnCore`
          -- selects exclusively from `runQueueOnCore`, never scanning ready
          -- TCBs, and an unbound thread is fully schedulable in this model —
          -- `resolveEffectivePrioDeadline`'s `.unbound` arm returns the legacy
          -- TCB priority rather than making the thread passive.  So a runnable
          -- thread was left ready and permanently unschedulable by a successful
          -- syscall.  Pre-existing and reachable on a single core: before the
          -- home-core fix above the same removal ran against `bootCoreId`.
          --
          -- Both entry shapes strand the thread, so both are repaired.  A thread
          -- that was **current** is not in the run queue (dequeue-on-dispatch),
          -- so clearing `current` leaves it nowhere; it is enqueued here.  A
          -- thread that was **queued** is removed and re-inserted at the legacy
          -- priority, which is the re-bucket the docstring always described.
          let updatedTcb := { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }
          let legacyPrio := updatedTcb.boostedPriority
          -- The current-slot stage is a scheduler-only update of the pre-state
          -- (`v0.35.71`): its object table IS the pre-state's, definitionally,
          -- so the witness the SchedContext lookup above carries is the stage's
          -- own and the rewrite below takes it directly.
          let st1 : SystemState := { st with scheduler := sched0 }
          -- Z5-H2 cont: Clear both sides of the binding
          -- **WS-HP HP10.4**: and the origin, for the bind's reason in the other
          -- direction — the reservation stops being owned at all, so a recorded
          -- departure from ownership has no subject.
          let updatedSc := { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }
          let st2 := st1.rewriteObject vScId.val (KernelObject.schedContext updatedSc)
            (SystemState.rewriteAdmissible_schedContext hSc updatedSc)
          -- The TCB through the typed rewrite over the rewritten state, for the
          -- reason `schedContextBind` gives: the record it writes is the stored
          -- one with its binding cleared, which is `updatedTcb` on every state
          -- the two lookups above admit.
          let st3 := st2.updateTcb tid fun t =>
            { t with scBindingScCode := 0, scBindingOwnerCode := 0 }
          -- The run-queue stage, after the object writes (it reads none of
          -- them): through the thread's TCB run-queue links (WS-ZA ZA4.5).
          -- The reschedule-SGI accumulator (KSC-1): a thread that was current
          -- is PLACED on its home here (a wake there, flagged as such); a
          -- queued thread is re-bucketed, and the key hook at the end flags
          -- its home exactly when the legacy key differs.
          let st3q := schedContextUnbindQueueStage st3 unbindHome tid legacyPrio wasCurrent
          -- Z5-H3: Remove SchedContext from replenish queue, on the core the
          -- context's own link names (WS-ZA ZA6.3).
          let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
          let st4 := purgeReplenishment st3q scIdTyped
          -- The reschedule-SGI accumulator (KSC-1): the thread's key is its
          -- legacy one now; a re-bucketed queued thread flags its home exactly
          -- when that differs from the reservation's key.  An unbound thread
          -- is always budget-eligible, so a queued thread whose reservation
          -- had run dry is one the chooser may now pick: the candidacy hook
          -- flags its cores (`markCandidacyGainFor`, against the pre-state).
          .ok ((), markKeyChangeFor (markCandidacyGainFor st4 tid (hasSufficientBudget st tcb))
            tid (effectiveSchedParams st tcb))
        -- Bound thread's TCB not found — clear SC side anyway
        | none =>
          -- **WS-HP HP10.4**: and the origin, for the bind's reason in the other
          -- direction — the reservation stops being owned at all, so a recorded
          -- departure from ownership has no subject.
          let updatedSc := { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }
          let st1 := st.rewriteObject vScId.val (KernelObject.schedContext updatedSc)
            (SystemState.rewriteAdmissible_schedContext hSc updatedSc)
          -- This arm is reached when the bound TCB is already gone from the
          -- store, so no home core can be named; the purge reads the core from
          -- the context's own link (WS-ZA ZA6.3), so it needs none.
          let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
          .ok ((), purgeReplenishment st1 scIdTyped)
    | none => .error .objectNotFound

/-- **WS-ZA ZA5.2**: `schedContextUnbind`'s checks: the context is stored and
binds a thread, and that thread, if stored, holds the context by binding rather
than by donation.  When they pass the operation's state is
`schedContextUnbindPerform` (`schedContextUnbind_of_admitted`). -/
@[inline] def schedContextUnbindAdmitted (st : SystemState) (vScId : ValidObjId) : Bool :=
  match st.getSchedContextWitnessed? (SchedContextId.ofObjId vScId.val) with
  | none => false
  | some ⟨sc, _⟩ =>
    match sc.boundThread with
    | none => false
    | some tid =>
      match st.getTcb? tid with
      | some tcb => !tcb.schedContextBinding.isDonated
      | none => true

/-- **WS-ZA ZA5.2**: `schedContextUnbind`'s writes, both success arms written
out over the same lookups. -/
@[inline] def schedContextUnbindPerform (st : SystemState) (vScId : ValidObjId) : SystemState :=
  match st.getSchedContextWitnessed? (SchedContextId.ofObjId vScId.val) with
  | none => st
  | some ⟨sc, hSc⟩ =>
    match sc.boundThread with
    | none => st
    | some tid =>
      match st.getTcb? tid with
      | some tcb =>
        let unbindHome := determineTargetCore st tid
        let runCore? := runningCoreOf? st tid
        let wasCurrent := runCore?.isSome
        let sched0 := match runCore? with
          | some runCore => (st.scheduler.setCurrentOnCore runCore none)
              |>.markReschedulePendingOnCore runCore
          | none => st.scheduler
        let updatedTcb := { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }
        let legacyPrio := updatedTcb.boostedPriority
        let st1 : SystemState := { st with scheduler := sched0 }
        let updatedSc := { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }
        let st2 := st1.rewriteObject vScId.val (KernelObject.schedContext updatedSc)
          (SystemState.rewriteAdmissible_schedContext hSc updatedSc)
        let st3 := st2.updateTcb tid fun t =>
          { t with scBindingScCode := 0, scBindingOwnerCode := 0 }
        let st3q := schedContextUnbindQueueStage st3 unbindHome tid legacyPrio wasCurrent
        let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
        let st4 := purgeReplenishment st3q scIdTyped
        markKeyChangeFor (markCandidacyGainFor st4 tid (hasSufficientBudget st tcb)) tid
          (effectiveSchedParams st tcb)
      | none =>
        let updatedSc := { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }
        let st1 := st.rewriteObject vScId.val (KernelObject.schedContext updatedSc)
          (SystemState.rewriteAdmissible_schedContext hSc updatedSc)
        let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
        purgeReplenishment st1 scIdTyped

/-- **WS-ZA ZA5.2**: an admitted unbind succeeds, and its state is the
perform's. -/
theorem schedContextUnbind_of_admitted (st : SystemState) (vScId : ValidObjId)
    (h : schedContextUnbindAdmitted st vScId = true) :
    schedContextUnbind vScId st = .ok ((), schedContextUnbindPerform st vScId) := by
  unfold schedContextUnbindAdmitted at h
  unfold schedContextUnbind schedContextUnbindPerform
  cases hW : st.getSchedContextWitnessed? (SchedContextId.ofObjId vScId.val) with
  | none => simp [hW] at h
  | some w =>
    obtain ⟨sc, hSc⟩ := w
    simp only [hW] at h ⊢
    cases hB : sc.boundThread with
    | none => simp [hB] at h
    | some tid =>
      simp only [hB] at h ⊢
      cases hT : st.getTcb? tid with
      | none => rfl
      | some tcb =>
        simp only [hT] at h ⊢
        have hD : tcb.schedContextBinding.isDonated = false := by simpa using h
        simp only [hD, Bool.false_eq_true, ↓reduceIte]

/-- **WS-ZA ZA5.2**: the unbind's scheduler write — the core running the
unbound thread loses it as current and is flagged to reschedule.  Compiled on
its own, so the state record is taken apart and rebuilt in one function and
its cell is reused; written inline in the perform, the record died in one join
point and was rebuilt in another, which allocates a fresh one. -/
def unbindVacateRunningCore (st : SystemState) (runCore? : Option Concurrency.CoreId) :
    SystemState :=
  { st with scheduler := match runCore? with
      | some runCore => (st.scheduler.setCurrentOnCore runCore none)
          |>.markReschedulePendingOnCore runCore
      | none => st.scheduler }

/-- **WS-ZA ZA5.2**: the compiled `schedContextUnbindPerform`.  The bound
thread is read from the context's code, and every read of the pre-state — the
home core, the core running the thread, its old key as three parts — is made
before the first write, so neither the state, the context nor the TCB is held
across a write and each is written in its slot
(`schedContextUnbindPerform_eq_impl`). -/
@[inline] def schedContextUnbindPerformImpl (st : SystemState) (vScId : ValidObjId) :
    SystemState :=
  match st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
  | none => st
  | some sc =>
    match sc.boundThreadCode with
    | 0 => st
    | k + 1 =>
      let tid : SeLe4n.ThreadId := ⟨k⟩
      let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
      let clear := fun (s : SchedContext) =>
        { s with boundThreadCode := 0, isActive := false, donationOrigin := none }
      match st.getTcb? tid with
      | some tcb =>
        let unbindHome := determineTargetCore st tid
        let runCore? := runningCoreOf? st tid
        let wasCurrent := runCore?.isSome
        let legacyPrio := tcb.boostedPriority
        let p0 := tcb.boostedPriority
        let d0 := effectiveDeadline st tcb
        let dom0 := tcb.domain
        let e0 := hasSufficientBudget st tcb
        let st1 := unbindVacateRunningCore st runCore?
        let st2 := st1.updateSchedContext (SchedContextId.ofObjId vScId.val) clear
        let st3 := st2.updateTcb tid fun t =>
          { t with scBindingScCode := 0, scBindingOwnerCode := 0 }
        let st3q := schedContextUnbindQueueStage st3 unbindHome tid legacyPrio wasCurrent
        let st4 := purgeReplenishment st3q scIdTyped
        markKeyChangeParts (markCandidacyGainFor st4 tid e0) tid p0 d0 dom0
      | none =>
        let st1 := st.updateSchedContext (SchedContextId.ofObjId vScId.val) clear
        purgeReplenishment st1 scIdTyped

@[csimp] theorem schedContextUnbindPerform_eq_impl :
    @schedContextUnbindPerform = @schedContextUnbindPerformImpl := by
  funext st vScId
  unfold schedContextUnbindPerform schedContextUnbindPerformImpl
  have hVal := SystemState.getSchedContextWitnessed?_val st (SchedContextId.ofObjId vScId.val)
  rcases hW : st.getSchedContextWitnessed? (SchedContextId.ofObjId vScId.val) with _ | ⟨sc, hS⟩
  · rw [hW] at hVal
    simp only [Option.map_none] at hVal
    simp only [← hVal]
  · simp only [hS]
    have hB : sc.boundThread = SeLe4n.ThreadId.ofOptCode sc.boundThreadCode := rfl
    rw [hB]
    rcases hC : sc.boundThreadCode with _ | k
    · rfl
    · simp only [SeLe4n.ThreadId.ofOptCode]
      cases hT : st.getTcb? (⟨k⟩ : SeLe4n.ThreadId) with
      | none =>
        dsimp only
        have hS' : st.getSchedContext? (SchedContextId.ofObjId vScId.val) = some sc := hS
        rw [SystemState.updateSchedContext_eq_of_some hS']
        rfl
      | some tcb =>
        dsimp only
        have hS1 : ∀ sch, ({ st with scheduler := sch } : SystemState).getSchedContext?
            (SchedContextId.ofObjId vScId.val) = some sc := fun _ => hS
        unfold unbindVacateRunningCore
        rw [SystemState.updateSchedContext_eq_of_some (hS1 _), markKeyChangeFor_eq_parts,
          effectiveSchedParams_eq_parts]
        rfl

-- ============================================================================
-- WS-RR RR8.12 Cut B2: the placement's payoff
-- ============================================================================

/-- A re-key leaves the thread on core `c`'s run queue. -/
private theorem runnableOnSomeCore_of_requeue (s : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId) (pr : SeLe4n.Priority)
    (hT : (s.getTcb? tid).isSome) :
    runnableOnSomeCore (s.runRequeueOnCore c tid pr) tid = true := by
  rw [runnableOnSomeCore]
  refine List.any_eq_true.mpr ⟨c, SeLe4n.Kernel.Concurrency.mem_allCores c, ?_⟩
  rw [SystemState.runRequeueOnCore_queuedOn, if_pos rfl, hT]
  simp

/-- The placement arm's shape: a link enqueue on core `c`, carrying the home
core's reschedule-pending mark (the KSC-1 accumulator) — the mark leaves every
run queue as it was. -/
private theorem runnableOnSomeCore_of_enqueue_marked (s : SystemState)
    (c c' : SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId) (pr : SeLe4n.Priority)
    (hT : (s.getTcb? tid).isSome) (hI : isIdleThreadId tid = false) :
    runnableOnSomeCore ((s.runEnqueueOnCore c tid pr).markReschedulePendingOnCore c') tid = true := by
  -- Admitted, the enqueue places the thread on `c`; declined, its links already
  -- name the core whose queue holds it.
  obtain ⟨c0, hc0⟩ := SystemState.runEnqueueOnCore_queuedOn_somewhere pr hT hI
  rw [runnableOnSomeCore]
  exact List.any_eq_true.mpr ⟨c0, SeLe4n.Kernel.Concurrency.mem_allCores c0, hc0⟩

/-- The bind's two object writes — the reservation rewrite and the thread's
binding — move no run-queue link, so they keep the link agreement and the
thread's TCB. -/
private theorem bindWrites_runQueueRefined (st : SystemState) (id : SeLe4n.ObjId)
    (sc' : SchedContext) (pf : st.rewriteAdmissible id (.schedContext sc'))
    (t : SeLe4n.ThreadId) (f : TCB → TCB) (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hT : (st.getTcb? t).isSome) :
    ((st.rewriteObject id (.schedContext sc') pf).updateTcb t f).runQueueRefined ∧
      (((st.rewriteObject id (.schedContext sc') pf).updateTcb t f).getTcb? t).isSome := by
  have hInv1 := SystemState.rewriteObject_preserves_objects_invExt st id _ pf hInv
  have hR1 : (st.rewriteObject id (.schedContext sc') pf).runQueueRefined :=
    SystemState.runQueueRefined_of_frame (st := st) (fun c x => by
      unfold SystemState.runLinkOn
      rw [SystemState.rewriteObject_schedContext_getTcb? st id sc' pf hInv]) rfl rfl hR
  refine ⟨SystemState.updateTcb_runQueueRefined hInv1 hf hR1, ?_⟩
  rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv1,
    SystemState.rewriteObject_schedContext_getTcb? st id sc' pf hInv]
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hT
  rw [hx]; rfl

/-- The bind's two object writes keep every thread's run-queue core. -/
private theorem bindWrites_runCoresAgree (st : SystemState) (id : SeLe4n.ObjId)
    (sc' : SchedContext) (pf : st.rewriteAdmissible id (.schedContext sc'))
    (t : SeLe4n.ThreadId) (f : TCB → TCB) (hf : ∀ x, (f x).runCoreCode = x.runCoreCode)
    (hInv : st.objects.invExt) :
    SystemState.RunCoresAgree ((st.rewriteObject id (.schedContext sc') pf).updateTcb t f) st :=
  SystemState.RunCoresAgree.trans
    (SystemState.updateTcb_runCoreCode _ t f hf
      (SystemState.rewriteObject_preserves_objects_invExt st id _ pf hInv))
    (fun y => by rw [SystemState.rewriteObject_schedContext_getTcb? st id sc' pf hInv])

/-- **Cut B2 (`v0.35.182`): a parked runnable thread the bind admits ends up on a
run queue.**

The statement the cut exists for, and the one whose negation was the registered
divergence: `chooseThreadOnCore` selects exclusively from `runQueueOnCore` and
never scans ready TCBs, so *on some core's run queue* is exactly *schedulable
again*.  Before this cut a bind left such a thread on none, and nothing else
could put it there — `.tcbResume` demands `.Inactive` and the reclaim that
parked it has already run.

Stated over `runnableOnSomeCore` rather than over the home core so it needs no
`invExt`: the transport of `determineTargetCore` across the bind's two object
writes is what would require one, and *which* queue the thread lands on is not
what the claim is about.  `schedContextBind_confinedToCores` already pins the
core, at the write set the footprint declares. -/
theorem schedContextBind_places_parked_thread
    (vScId : ValidObjId) (vThreadId : ValidThreadId) (st st' : SystemState) (tcb : TCB)
    (scB : SchedContext)
    (hTcb : st.getTcb? vThreadId.val = some tcb)
    (hScB : st.getSchedContext? (SchedContextId.ofObjId vScId.val) = some scB)
    (hPark : bindPlacesParkedThread st vThreadId.val tcb (scB.releaseReadyHead st.machine.timer)
      = true)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined)
    (h : schedContextBind vScId vThreadId st = .ok ((), st')) :
    runnableOnSomeCore st' vThreadId.val = true := by
  unfold schedContextBind at h
  split at h
  · rename_i sc hSc _
    obtain rfl : sc = scB := by rw [hSc] at hScB; exact Option.some.inj hScB
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · rename_i tcb' hTcb'
          obtain rfl : tcb' = tcb := by rw [hTcb'] at hTcb; exact Option.some.inj hTcb
          split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · split at h
              · dsimp only at h
                rw [Except.ok.injEq, Prod.mk.injEq] at h
                rw [← h.2, releasePlace_runnableOnSomeCore, markKeyChangeFor_runnableOnSomeCore]
                -- The guard transports from the pre-state: both of the bind's
                -- writes are object rewrites, so the intermediate state's
                -- scheduler IS the pre-state's.
                have hSched : ∀ (a : SystemState) (b : SeLe4n.ObjId) (o : KernelObject)
                    (pf : _) (f : TCB → TCB),
                    ((a.rewriteObject b o pf).updateTcb vThreadId.val f).scheduler
                      = a.scheduler := by
                  intro a b o pf f
                  rw [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
                split
                · -- The re-bucket arm: the thread was already queued, so it stays.
                  exact runnableOnSomeCore_of_requeue _ _ _ _ (bindWrites_runQueueRefined st _ _ _ _ _
                    (by intro _ _; rfl) hInv hR (by rw [hTcb]; rfl)).2
                · split
                  · -- The placement arm: Cut B2's own write.
                    rename_i hPlace
                    refine runnableOnSomeCore_of_enqueue_marked _ _ _ _ _ ?_
                      (bindPlacesParkedThread_not_idle hPlace)
                    exact (bindWrites_runQueueRefined st _ _ _ _ _
                      (by intro _ _; rfl) hInv hR (by rw [hTcb]; rfl)).2
                  · -- The identity arm is UNREACHABLE under the hypothesis: the
                    -- guard is the pre-state's, which this arm's condition denies.
                    rename_i hParkArm
                    exfalso
                    rw [bindPlacesParkedThread_congr _ _ _ (hSched _ _ _ _ _)
                      (bindWrites_runCoresAgree st _ _ _ _ _ ?_ hInv)] at hParkArm
                    rotate_left; · intro _; rfl
                    rw [hPark] at hParkArm
                    simp at hParkArm
              · exact absurd h (by simp)
        · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **PR #900 review (`v0.36.1`): a bind places no thread on a reservation with no
budget.**

The negation Cut B2 left open: the placement arm admitted a parked thread whatever
the reservation's budget, so binding an **exhausted** one — reachable by unbinding
it mid-period, which keeps `budgetRemaining = 0` and purges its replenishment
entry — put the thread on a run queue `chooseBestRunnableEffective` skips it on,
with no refill ever due, while the bind reported success.  Here a thread the bind
finds on no scheduler slot stays on none when the reservation's budget is zero
once its head refill released by now is taken (WS-ZA ZA6.4: the bind then
postpones the context on the release queue, so the refill wakes the thread);
the re-bucket arm cannot fire (the thread is on no run queue), the placement arm
cannot (its fourth conjunct is false), and the identity arm moves no slot.

Stated over `placedCoreOf?`, which reads the scheduler alone, so the claim covers
the current slots as well as the run queues and needs no object-store invariant. -/
theorem schedContextBind_leaves_unplaced_of_exhausted
    (vScId : ValidObjId) (vThreadId : ValidThreadId) (st st' : SystemState)
    (scB : SchedContext)
    (hScB : st.getSchedContext? (SchedContextId.ofObjId vScId.val) = some scB)
    (hExhausted : (scB.releaseReadyHead st.machine.timer).budgetRemaining.isPositive = false)
    (hUnplaced : placedCoreOf? st vThreadId.val = none)
    (hInv : st.objects.invExt)
    (h : schedContextBind vScId vThreadId st = .ok ((), st')) :
    placedCoreOf? st' vThreadId.val = none := by
  -- `placedCoreOf?` reads the scheduler and the thread's run-queue core.
  have hPlacedCongr : ∀ (a b : SystemState), a.scheduler = b.scheduler →
      SystemState.RunCoresAgree a b →
      placedCoreOf? a vThreadId.val = placedCoreOf? b vThreadId.val := by
    intro a b hab hQ
    unfold placedCoreOf?
    have hF : (fun c => a.queuedOn c vThreadId.val ||
          a.scheduler.currentOnCore c == some vThreadId.val) =
        (fun c => b.queuedOn c vThreadId.val ||
          b.scheduler.currentOnCore c == some vThreadId.val) := by
      funext c; rw [hQ.queuedOn, hab]
    rw [hF]
  -- A thread placed nowhere is on no run queue.
  have hNotQueued : ∀ c, st.queuedOn c vThreadId.val = false := by
    intro c
    unfold placedCoreOf? at hUnplaced
    rw [List.find?_eq_none] at hUnplaced
    have := hUnplaced c (SeLe4n.Kernel.Concurrency.mem_allCores c)
    simp only [Bool.or_eq_true, not_or] at this
    exact Bool.eq_false_iff.mpr this.1
  unfold schedContextBind at h
  split at h
  · rename_i sc hSc _
    obtain rfl : sc = scB := by rw [hSc] at hScB; exact Option.some.inj hScB
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · rename_i tcb _
          split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · split at h
              · dsimp only at h
                rw [Except.ok.injEq, Prod.mk.injEq] at h
                rw [← h.2, releasePlace_placedCoreOf?, markKeyChangeFor_placedCoreOf?]
                have hSched : ∀ (a : SystemState) (b : SeLe4n.ObjId) (o : KernelObject)
                    (pf : _) (f : TCB → TCB),
                    ((a.rewriteObject b o pf).updateTcb vThreadId.val f).scheduler
                      = a.scheduler := by
                  intro a b o pf f
                  rw [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
                split
                · -- The re-bucket arm needs the thread on a run queue, which it is not.
                  rename_i hMem
                  exfalso
                  rw [(bindWrites_runCoresAgree st _ _ _ _ _ ?_ hInv).queuedOn,
                    hNotQueued] at hMem
                  · exact Bool.false_ne_true hMem
                  · intro _; rfl
                · split
                  · -- The placement arm needs the guard, whose budget conjunct is false.
                    rename_i hParkArm
                    exfalso
                    rw [bindPlacesParkedThread_of_exhausted _ _ _ _ hExhausted] at hParkArm
                    exact Bool.false_ne_true hParkArm
                  · -- The identity arm moves no scheduler slot.
                    refine (hPlacedCongr _ st ?_ ?_).trans hUnplaced
                    · show (((st.rewriteObject _ _ _).updateTcb _ _).scheduler) = st.scheduler
                      exact hSched _ _ _ _ _
                    · exact SystemState.RunCoresAgree.trans (SystemState.RunCoresAgree.of_objects rfl)
                        (bindWrites_runCoresAgree st _ _ _ _ _ (by intro _; rfl) hInv)
              · exact absurd h (by simp)
        · exact absurd h (by simp)
  · exact absurd h (by simp)


-- ============================================================================
-- The unbind's run-queue agreement and current placement (WS-ZA ZA4.5)
-- ============================================================================

/-- The unbind's run-queue stage keeps the run queues in agreement with the
links: a re-key of a thread its home queue holds, or a guarded enqueue. -/
theorem schedContextUnbindQueueStage_runQueueLinkStage (st0 : SystemState)
    (home : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool) :
    SystemState.RunQueueLinkStage st0 (schedContextUnbindQueueStage st0 home tid prio wasCurrent) := by
  unfold schedContextUnbindQueueStage
  split
  · rename_i hMem
    have hq : (st0.runLinkOn home tid).queued = true := by
      rw [← SystemState.queuedOn_eq_runLinkOn]; exact hMem
    exact (SystemState.RunQueueStage.runRequeueOnCore _ _ _ _ hq).1
  · split
    · exact (SystemState.RunQueueLinkStage.runEnqueueOnCore _ _ _ _).trans
        (SystemState.RunQueueStage.markReschedulePendingOnCore _ home).1
    · exact .refl _

/-- ...and, for a thread current on no core and runnable if it was current, a
stage. -/
theorem schedContextUnbindQueueStage_runQueueStage (st0 : SystemState)
    (home : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool)
    (hNC : ∀ c, st0.scheduler.currentOnCore c ≠ some tid)
    (hRun : wasCurrent = true → st0.runnable tid)
    (hHome : wasCurrent = true → st0.homedOn tid home) :
    SystemState.RunQueueStage st0 (schedContextUnbindQueueStage st0 home tid prio wasCurrent) := by
  unfold schedContextUnbindQueueStage
  split
  · rename_i hMem
    have hq : (st0.runLinkOn home tid).queued = true := by
      rw [← SystemState.queuedOn_eq_runLinkOn]; exact hMem
    exact SystemState.RunQueueStage.runRequeueOnCore _ _ _ _ hq
  · split
    · rename_i hW
      exact (SystemState.RunQueueStage.runEnqueueOnCore _ _ _ _ hNC (hRun hW) (hHome hW)).trans
        (SystemState.RunQueueStage.markReschedulePendingOnCore _ home)
    · exact .refl _

/-- WS-ZA ZA6.4: **the unbind's close** — after the context `s` is stored
unbound (`u`) and its thread's queue placement is written, the purge leaves `s`
unbound and on no queue, so a state sound off `S` and `s` is sound off `S`. -/
theorem schedContextUnbind_close {S : SchedContextId → Prop} {st st3q : SystemState}
    {s : SchedContextId} {sc u : SchedContext} (hSc : st.getSchedContext? s = some sc)
    (hs : ¬ S s) (h0 : st.refillsSoundExcept S)
    (hu : u = { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
    (hR4 : (purgeReplenishment st3q s).releaseQueueRefined)
    (h4 : (purgeReplenishment st3q s).refillsSoundExcept (fun x => S x ∨ x = s))
    (hV : ∀ a, st3q.getSchedContext? s = some a → a.refillView = u.refillView) :
    (purgeReplenishment st3q s).refillsSoundExcept S := by
  have hKp := RefillViewsKept.of_agreeOffReleaseLinks (purgeReplenishment_agree st3q s)
  refine SystemState.refillsSoundExcept_close_unbound (u := u) h4 (fun a ha => ?_)
    (by subst hu; rfl) (by subst hu; exact h0.1 s sc hs hSc) (fun c e he hes => ?_)
  · obtain ⟨b, hb, hv⟩ := hKp.getSchedContext? ha
    exact hv.symm.trans (hV b hb)
  · exact SystemState.not_mem_entries_of_not_queued hR4
      (SystemState.releaseRemoveAnywhere_not_queued st3q s) c e he hes

/-- The context the unbind stores is the one its purge reads: the thread write
and the queue stage after it keep every context. -/
theorem schedContextUnbind_storedView {st1 : SystemState} {k : SeLe4n.ObjId} {u : SchedContext}
    {h : st1.rewriteAdmissible k (.schedContext u)} (hI : st1.objects.invExt)
    (tid : SeLe4n.ThreadId) (f : TCB → TCB) (home : Concurrency.CoreId) (tid' : SeLe4n.ThreadId)
    (prio : SeLe4n.Priority) (wc : Bool) (a : SchedContext)
    (ha : (schedContextUnbindQueueStage ((st1.rewriteObject k (.schedContext u) h).updateTcb tid f)
      home tid' prio wc).getSchedContext? (SchedContextId.ofObjId k) = some a) :
    a.refillView = u.refillView := by
  obtain ⟨b, hb, hv⟩ := ((RefillViewsKept.of_agreeOffRunLinks
    (schedContextUnbindQueueStage_objectsAgreeOffRunLinks _ _ _ _ _)).trans
    (.of_getSchedContext?_eq (SystemState.updateTcb_getSchedContext? _ _ _
      (SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hI)))).getSchedContext? ha
  cases Option.some.inj ((SystemState.rewriteObject_schedContext_getSchedContext?_self st1
    (SchedContextId.ofObjId k) u h hI).symm.trans hb)
  exact hv.symm

/-- The unbind's close as a stage: a frame off `s` up to the state the purge
runs on, whose context `s` is the unbound `u`, is a stage up to the purge. -/
theorem schedContextUnbind_linkStage_close {st st3q : SystemState} {s : SchedContextId}
    {sc u : SchedContext} (hSc : st.getSchedContext? s = some sc)
    (hu : u = { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
    (hF : SystemState.RunQueueLinkFrame (· = s) st st3q)
    (hV : st.objects.invExt → ∀ a, st3q.getSchedContext? s = some a → a.refillView = u.refillView) :
    SystemState.RunQueueLinkStage st (purgeReplenishment st3q s) :=
  SystemState.RunQueueLinkFrame.withRefills (hF.trans (purgeReplenishment_runQueueFrameStage st3q s).1)
    fun _ hs hI _ _ _ hR4 h0 h4 => schedContextUnbind_close hSc hs h0 hu hR4 h4 (hV hI)

/-- `schedContextUnbind_linkStage_close` for a frame stage. -/
theorem schedContextUnbind_stage_close {st st3q : SystemState} {s : SchedContextId}
    {sc u : SchedContext} (hSc : st.getSchedContext? s = some sc)
    (hu : u = { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
    (hF : SystemState.RunQueueFrameStage (· = s) st st3q)
    (hV : st.objects.invExt → ∀ a, st3q.getSchedContext? s = some a → a.refillView = u.refillView) :
    SystemState.RunQueueStage st (purgeReplenishment st3q s) :=
  SystemState.RunQueueFrameStage.withRefills (hF.trans (purgeReplenishment_runQueueFrameStage st3q s))
    fun _ hs hI _ _ _ hR4 h0 h4 => schedContextUnbind_close hSc hs h0 hu hR4 h4 (hV hI)

/-- The unbind keeps the link agreement. -/
theorem schedContextUnbind_runQueueLinkStage (vScId : SeLe4n.ValidObjId) (st st' : SystemState)
    (hStep : schedContextUnbind vScId st = .ok ((), st')) : SystemState.RunQueueLinkStage st st' := by
  unfold schedContextUnbind at hStep
  split at hStep
  · rename_i sc hSc _
    split at hStep
    · contradiction
    · rename_i tid hBound
      split at hStep
      · rename_i tcb hTcb
        dsimp only [] at hStep
        split at hStep
        · contradiction
        · have hScRaw := (SystemState.getSchedContext?_eq_some_iff st
            (SchedContextId.ofObjId vScId.val) sc).mp hSc
          cases hStep
          have hVac : SystemState.RunQueueStage st { st with scheduler := match runningCoreOf? st tid with
              | some r => (st.scheduler.setCurrentOnCore r none).markReschedulePendingOnCore r
              | none => st.scheduler } :=
            SystemState.RunQueueStage.of_frame_vacate rfl (by split <;> rfl) (by split <;> rfl)
              (fun c y h' => by
                revert h'; split
                · rename_i r _; intro h'
                  by_cases hrc : r = c
                  · subst hrc; simp at h'
                  · rwa [SchedulerState.markReschedulePendingOnCore_currentOnCore,
                      SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hrc] at h'
                · exact id)
          refine SystemState.RunQueueLinkStage.trans ?_ (.of_stage (markKeyChangeFor_runQueueStage _ _ _))
          refine SystemState.RunQueueLinkStage.trans ?_
            (.of_stage (markCandidacyGainFor_runQueueStage _ _ _))
          refine schedContextUnbind_linkStage_close hSc rfl ?_ fun hI =>
            schedContextUnbind_storedView (by exact hI) _ _ _ _ _ _
          refine SystemState.RunQueueLinkFrame.trans (st' := SystemState.updateTcb _ _ _) ?_
            (SystemState.RunQueueLinkStage.toFrame (schedContextUnbindQueueStage_runQueueLinkStage _ _ _ _ _) _)
          refine SystemState.RunQueueLinkFrame.trans (st' := SystemState.rewriteObject _ _ _ _) ?_
            (SystemState.RunQueueLinkStage.toFrame (.of_stage (SystemState.RunQueueStage.updateTcb _ _
              (f := fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 })
              (by intro _ _; rfl))) _)
          refine SystemState.RunQueueLinkFrame.trans
            (st' := { st with scheduler := match runningCoreOf? st tid with
              | some r => (st.scheduler.setCurrentOnCore r none).markReschedulePendingOnCore r
              | none => st.scheduler })
            (SystemState.RunQueueLinkStage.toFrame (.of_stage hVac) _) ?_
          refine (?_ : SystemState.RunQueueFrameStage _ _ _).1
          exact SystemState.RunQueueFrameStage.insert rfl rfl rfl
            (fun c => by dsimp only; rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
              (SystemState.objStateMono_nonTcb (by dsimp only; rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl) rfl) (hB := by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
            (hR := fun _ => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
            (hY := by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
      · dsimp only [] at hStep
        cases hStep
        have hScRaw := (SystemState.getSchedContext?_eq_some_iff st
          (SchedContextId.ofObjId vScId.val) sc).mp hSc
        refine SystemState.RunQueueLinkStage.of_stage ?_
        refine schedContextUnbind_stage_close hSc rfl ?_ (fun hI a ha => by
          cases Option.some.inj ((SystemState.rewriteObject_schedContext_getSchedContext?_self st
            (SchedContextId.ofObjId vScId.val) _ _ hI).symm.trans ha)
          rfl)
        exact SystemState.RunQueueFrameStage.insert rfl rfl rfl
          (fun c => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
          (SystemState.objStateMono_nonTcb (by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl) rfl) (hB := by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
              (hR := fun _ => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
              (hY := by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
  · contradiction


/-- Between scheduling points the unbind is a run-queue stage: its queue stage
needs the bound thread current on at most the core that runs it. -/
theorem schedContextUnbind_runQueueStage_of_dequeued (vScId : SeLe4n.ValidObjId) (st st' : SystemState)
    (hD : st.currentDequeuedUnique)
    (hStep : schedContextUnbind vScId st = .ok ((), st')) : SystemState.RunQueueStage st st' := by
  unfold schedContextUnbind at hStep
  split at hStep
  · rename_i sc hSc _
    split at hStep
    · contradiction
    · rename_i tid hBound
      split at hStep
      · rename_i tcb hTcb
        dsimp only [] at hStep
        split at hStep
        · contradiction
        · have hScRaw := (SystemState.getSchedContext?_eq_some_iff st
            (SchedContextId.ofObjId vScId.val) sc).mp hSc
          cases hStep
          have hVac : SystemState.RunQueueStage st { st with scheduler := match runningCoreOf? st tid with
              | some r => (st.scheduler.setCurrentOnCore r none).markReschedulePendingOnCore r
              | none => st.scheduler } :=
            SystemState.RunQueueStage.of_frame_vacate rfl (by split <;> rfl) (by split <;> rfl)
              (fun c y h' => by
                revert h'; split
                · rename_i r _; intro h'
                  by_cases hrc : r = c
                  · subst hrc; simp at h'
                  · rwa [SchedulerState.markReschedulePendingOnCore_currentOnCore,
                      SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hrc] at h'
                · exact id)
          refine SystemState.RunQueueStage.of_invExt fun hInv => ?_
          have hNC : ∀ c, ({ st with scheduler := match runningCoreOf? st tid with
              | some r => (st.scheduler.setCurrentOnCore r none).markReschedulePendingOnCore r
              | none => st.scheduler } : SystemState).scheduler.currentOnCore c ≠ some tid := by
            intro c hc
            cases hRC : runningCoreOf? st tid with
            | none =>
              simp only [hRC] at hc
              exact runningCoreOf?_none_currentOnCore hRC c hc
            | some r =>
              have hCurR := runningCoreOf?_some_currentOnCore hRC
              simp only [hRC] at hc
              by_cases hrc : r = c
              · subst hrc; simp at hc
              · rw [SchedulerState.markReschedulePendingOnCore_currentOnCore,
                  SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hrc] at hc
                exact hrc ((hD.current c tid hc).2.1 r hCurR)
          refine SystemState.RunQueueStage.trans ?_ (markKeyChangeFor_runQueueStage _ _ _)
          refine SystemState.RunQueueStage.trans ?_ (markCandidacyGainFor_runQueueStage _ _ _)
          refine schedContextUnbind_stage_close hSc rfl ?_ fun hI =>
            schedContextUnbind_storedView (by exact hI) _ _ _ _ _ _
          refine SystemState.RunQueueFrameStage.trans (st' := SystemState.updateTcb _ _ _) ?_
            (SystemState.RunQueueStage.toFrame (schedContextUnbindQueueStage_runQueueStage _ _ _ _ _ (by simpa only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler] using hNC)
              (fun hW => ?hRun) (fun hW => ?hHome)) _)
          refine SystemState.RunQueueFrameStage.trans (st' := SystemState.rewriteObject _ _ _ _) ?_
            (SystemState.RunQueueStage.toFrame (SystemState.RunQueueStage.updateTcb _ _
              (f := fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 })
              (by intro _ _; rfl)) _)
          refine SystemState.RunQueueFrameStage.trans
            (st' := { st with scheduler := match runningCoreOf? st tid with
              | some r => (st.scheduler.setCurrentOnCore r none).markReschedulePendingOnCore r
              | none => st.scheduler })
            (SystemState.RunQueueStage.toFrame hVac _) ?_
          · exact SystemState.RunQueueFrameStage.insert rfl rfl rfl
              (fun c => by dsimp only; rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
              (SystemState.objStateMono_nonTcb (by dsimp only; rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl) rfl) (hB := by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
              (hR := fun _ => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
              (hY := by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
          case hRun =>
            obtain ⟨r, hRC⟩ := Option.isSome_iff_exists.mp hW
            have hR0 := hD.runnable (runningCoreOf?_some_currentOnCore hRC)
            exact (((SystemState.StateMono.of_objects rfl).trans
              ((SystemState.StateMono.insert hInv rfl
                (SystemState.objStateMono_nonTcb (by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl) rfl)).trans
              (SystemState.StateMono.updateTcb (RHTable_insert_preserves_invExt _ _ _ hInv) tid (by tcb_state_mono)))) tid).1 hR0
          case hHome =>
            obtain ⟨r, hRC⟩ := Option.isSome_iff_exists.mp hW
            have hR0 := hD.runnable (runningCoreOf?_some_currentOnCore hRC)
            exact ((SystemState.StateMono.of_objects rfl).trans
              ((SystemState.StateMono.insert hInv rfl
                (SystemState.objStateMono_nonTcb (by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl) rfl)).trans
              (SystemState.StateMono.updateTcb (RHTable_insert_preserves_invExt _ _ _ hInv) tid (by tcb_state_mono)))).homedOn
              hR0.activeAt (homedOn_determineTargetCore st tid)
      · dsimp only [] at hStep
        cases hStep
        have hScRaw := (SystemState.getSchedContext?_eq_some_iff st
          (SchedContextId.ofObjId vScId.val) sc).mp hSc
        refine schedContextUnbind_stage_close hSc rfl ?_ (fun hI a ha => by
          cases Option.some.inj ((SystemState.rewriteObject_schedContext_getSchedContext?_self st
            (SchedContextId.ofObjId vScId.val) _ _ hI).symm.trans ha)
          rfl)
        exact SystemState.RunQueueFrameStage.insert rfl rfl rfl
          (fun c => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
          (SystemState.objStateMono_nonTcb (by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl) rfl) (hB := by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
              (hR := fun _ => by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
              (hY := by rw [show st.objects[vScId.val]? = _ from hScRaw]; rfl)
  · contradiction


/-- The unbind keeps the run queues in agreement with the links: the current
slot and the flag are not read by it, the two object writes move no link, and
the queue stage is one (`schedContextUnbindQueueStage_runQueueStage`). -/
theorem schedContextUnbind_runQueueEntryStage (vScId : SeLe4n.ValidObjId) (st st' : SystemState)
    (hStep : schedContextUnbind vScId st = .ok ((), st')) : SystemState.RunQueueEntryStage st st' :=
  SystemState.RunQueueEntryStage.of_cond (schedContextUnbind_runQueueLinkStage vScId st st' hStep)
    fun hD => schedContextUnbind_runQueueStage_of_dequeued vScId st st' hD hStep

end SeLe4n.Kernel.SchedContextOps
