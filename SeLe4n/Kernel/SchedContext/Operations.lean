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
import SeLe4n.Model.State

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
- `schedContextYieldTo`: Budget transfer between SchedContexts (kernel-internal)
-/

namespace SeLe4n.Kernel.SchedContextOps

open SeLe4n
open SeLe4n.Kernel.Concurrency (bootCoreId)
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- WS-SM SM8.B: per-core replenish-queue purging
-- ============================================================================

/-- WS-SM SM8.B (PR #861 review round 17): the core whose replenish queue holds
`sc`'s eligibility entry.

Replenishments are enqueued **per core** — `replenishOnCore` writes
`replenishQueueOnCore c` for the core the SC's bound thread runs on — and drained
per core by that core's timer tick.  So an SC's entry lives on its bound
thread's home core, not on the boot core; an affinity change moves it
(`migrateSchedContextReplenishment`), which is what keeps this reading true
rather than merely true at bind time.

An SC with no bound thread has no home, and also no live replenishment to
strand, so the boot core is the right default — the same one
`determineTargetCore` itself falls back to. -/
def schedContextReplenishHome (st : SystemState) (sc : SchedContext) :
    SeLe4n.Kernel.Concurrency.CoreId :=
  match sc.boundThread with
  | some boundTid => determineTargetCore st boundTid
  | none => bootCoreId

/-- WS-SM SM8.B: drop `scId`'s replenishment from core `c`'s queue. -/
def purgeReplenishmentOnCore (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (scId : SchedContextId) : SystemState :=
  let cleaned := ReplenishQueue.remove (st.scheduler.replenishQueueOnCore c) scId
  { st with scheduler := st.scheduler.setReplenishQueueOnCore c cleaned }

/-- WS-SM SM8.B: drop `scId`'s replenishment from **every** core's queue.

The form for a purge whose home core cannot be computed — an unbind whose bound
TCB is already gone from the store has no `cpuAffinity` left to read, so there
is no core to name and the only sound answer is all of them.  Same shape, and
the same reasoning, as `removeRunnableFromAllCores` on the destroy path. -/
def purgeReplenishmentFromAllCores (st : SystemState)
    (scId : SchedContextId) : SystemState :=
  SeLe4n.Kernel.Concurrency.allCores.foldl
    (fun s c => purgeReplenishmentOnCore s c scId) st

/-! ### Frames

The replenish queue is **not** one of the six `observableSlotsConfinedToCores`
slots, so both purges are invisible to per-core confinement — at every core,
including the one written.  Stated as `@[simp]` frames on the helpers rather
than left to unfold at each use site, so the confinement proofs reason about
the purge as a unit and a later change to its body cannot silently escape
them. -/

@[simp] theorem purgeReplenishmentOnCore_machine (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (scId : SchedContextId) :
    (purgeReplenishmentOnCore st c scId).machine = st.machine := rfl

@[simp] theorem purgeReplenishmentOnCore_currentOnCore (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (scId : SchedContextId)
    (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishmentOnCore st c scId).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  simp [purgeReplenishmentOnCore, SchedulerState.setReplenishQueueOnCore_currentOnCore]

@[simp] theorem purgeReplenishmentOnCore_runQueueOnCore (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (scId : SchedContextId)
    (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishmentOnCore st c scId).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
  simp [purgeReplenishmentOnCore, SchedulerState.setReplenishQueueOnCore_runQueueOnCore]

@[simp] theorem purgeReplenishmentOnCore_activeDomainOnCore (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (scId : SchedContextId)
    (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishmentOnCore st c scId).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' := by
  simp [purgeReplenishmentOnCore, SchedulerState.setReplenishQueueOnCore_activeDomainOnCore]

@[simp] theorem purgeReplenishmentOnCore_domainTimeRemainingOnCore (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (scId : SchedContextId)
    (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishmentOnCore st c scId).scheduler.domainTimeRemainingOnCore c'
      = st.scheduler.domainTimeRemainingOnCore c' := by
  simp [purgeReplenishmentOnCore,
    SchedulerState.setReplenishQueueOnCore_domainTimeRemainingOnCore]

@[simp] theorem purgeReplenishmentOnCore_domainScheduleIndexOnCore (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (scId : SchedContextId)
    (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishmentOnCore st c scId).scheduler.domainScheduleIndexOnCore c'
      = st.scheduler.domainScheduleIndexOnCore c' := by
  simp [purgeReplenishmentOnCore,
    SchedulerState.setReplenishQueueOnCore_domainScheduleIndexOnCore]

@[simp] theorem purgeReplenishmentOnCore_objects (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (scId : SchedContextId) :
    (purgeReplenishmentOnCore st c scId).objects = st.objects := rfl

/-- The sweep inherits every frame above, one fold step at a time. -/
private theorem purgeReplenishmentFromAllCores_frame
    {α : Type} (f : SystemState → α) (scId : SchedContextId)
    (hStep : ∀ (s : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId),
      f (purgeReplenishmentOnCore s c scId) = f s) (st : SystemState) :
    f (purgeReplenishmentFromAllCores st scId) = f st := by
  unfold purgeReplenishmentFromAllCores
  generalize SeLe4n.Kernel.Concurrency.allCores = cores
  induction cores generalizing st with
  | nil => rfl
  | cons hd tl ih => rw [List.foldl_cons, ih, hStep]

@[simp] theorem purgeReplenishmentFromAllCores_machine (st : SystemState)
    (scId : SchedContextId) :
    (purgeReplenishmentFromAllCores st scId).machine = st.machine :=
  purgeReplenishmentFromAllCores_frame (·.machine) scId (fun _ _ => rfl) st

@[simp] theorem purgeReplenishmentFromAllCores_currentOnCore (st : SystemState)
    (scId : SchedContextId) (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishmentFromAllCores st scId).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' :=
  purgeReplenishmentFromAllCores_frame (·.scheduler.currentOnCore c') scId
    (fun s c => purgeReplenishmentOnCore_currentOnCore s c scId c') st

@[simp] theorem purgeReplenishmentFromAllCores_runQueueOnCore (st : SystemState)
    (scId : SchedContextId) (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishmentFromAllCores st scId).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' :=
  purgeReplenishmentFromAllCores_frame (·.scheduler.runQueueOnCore c') scId
    (fun s c => purgeReplenishmentOnCore_runQueueOnCore s c scId c') st

@[simp] theorem purgeReplenishmentFromAllCores_activeDomainOnCore (st : SystemState)
    (scId : SchedContextId) (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishmentFromAllCores st scId).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' :=
  purgeReplenishmentFromAllCores_frame (·.scheduler.activeDomainOnCore c') scId
    (fun s c => purgeReplenishmentOnCore_activeDomainOnCore s c scId c') st

@[simp] theorem purgeReplenishmentFromAllCores_domainTimeRemainingOnCore (st : SystemState)
    (scId : SchedContextId) (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishmentFromAllCores st scId).scheduler.domainTimeRemainingOnCore c'
      = st.scheduler.domainTimeRemainingOnCore c' :=
  purgeReplenishmentFromAllCores_frame (·.scheduler.domainTimeRemainingOnCore c') scId
    (fun s c => purgeReplenishmentOnCore_domainTimeRemainingOnCore s c scId c') st

@[simp] theorem purgeReplenishmentFromAllCores_domainScheduleIndexOnCore (st : SystemState)
    (scId : SchedContextId) (c' : SeLe4n.Kernel.Concurrency.CoreId) :
    (purgeReplenishmentFromAllCores st scId).scheduler.domainScheduleIndexOnCore c'
      = st.scheduler.domainScheduleIndexOnCore c' :=
  purgeReplenishmentFromAllCores_frame (·.scheduler.domainScheduleIndexOnCore c') scId
    (fun s c => purgeReplenishmentOnCore_domainScheduleIndexOnCore s c scId c') st

@[simp] theorem purgeReplenishmentFromAllCores_objects (st : SystemState)
    (scId : SchedContextId) :
    (purgeReplenishmentFromAllCores st scId).objects = st.objects :=
  purgeReplenishmentFromAllCores_frame (·.objects) scId (fun _ _ => rfl) st

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

-- ============================================================================
-- Z5-F3: schedContextConfigure
-- ============================================================================

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

**AL8 (WS-AL / AK7-E.cascade) — Type-level validity discipline**: the
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
        let updated : SchedContext :=
          { sc with
            budget := ⟨budget⟩
            period := ⟨period⟩
            priority := ⟨priority⟩
            deadline := ⟨deadline⟩
            domain := ⟨domain⟩
            budgetRemaining := ⟨budget⟩
            -- AE3-F/U-14: Reset replenishment list to a single fresh entry
            -- with the new budget amount. Prevents stale entries from prior
            -- configuration referencing outdated budget/period values.
            -- AK6-C (SC-M02): The fresh replenishment becomes eligible one
            -- FULL period AFTER reconfigure (`timer + period.val`), not at
            -- the current timer instant. Otherwise a reconfigured SC would
            -- receive `budgetRemaining := budget` AND an immediately-eligible
            -- replenishment of `amount := budget`, giving it two full budgets
            -- per period and doubling its effective CBS bandwidth.
            replenishments := [{ amount := ⟨budget⟩,
                                 eligibleAt := st.machine.timer + period }] }
        if checkAdmission st updated (some vScId.val) then
          -- AK2-G: purge stale system replenishQueue entries for this vScId.val
          -- before storing the reconfigured object.
          let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
          -- WS-SM SM8.B (PR #861 review round 17): purge on the SC's HOME core.
          -- Keyed on `bootCoreId` this was a silent no-op for an SC whose bound
          -- thread runs anywhere else: the reconfigure installed a fresh
          -- replenishment eligible one period out while the *old* entry stayed
          -- queued on the home core, which still fired it — two budgets in the
          -- first period, defeating the reset and breaking CBS bandwidth
          -- isolation.  The same defect round 13 found in this operation's
          -- run-queue re-bucketing, one field over.
          let stCleaned := purgeReplenishmentOnCore st (schedContextReplenishHome st sc) scIdTyped
          -- AK2-B option B (S-H04): if the SchedContext is currently bound to a
          -- thread and configure changes the SC priority, propagate the new
          -- priority into the bound TCB's `priority` field AND re-bucket the
          -- thread in the RunQueue if present (so `schedulerPriorityMatch`'s
          -- `threadPriority[tid]? = effectiveRunQueuePriority tcb` continues to
          -- hold under the new TCB priority). Without the RunQueue migration
          -- the thread would remain in the old priority bucket while
          -- `tcb.priority` was updated — a latent priority-inversion vector.
          -- We preserve any existing `pipBoost` by re-inserting at
          -- `max(new priority, pipBoost)`, matching `migrateRunQueueBucket`
          -- in `PriorityManagement.lean`.
          match storeObject vScId.val (KernelObject.schedContext updated) stCleaned with
          | .error e => .error e
          | .ok ((), stStored) =>
            match sc.boundThread with
            | none => .ok ((), stStored)
            | some boundTid =>
              -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
              match stStored.getTcb? boundTid with
              | some boundTcb =>
                let stProp : SystemState :=
                  if boundTcb.priority.val = priority then
                    stStored  -- priority already consistent: no priority propagation needed
                  else
                    let newPri : SeLe4n.Priority := ⟨priority⟩
                    let boundTcb2 : TCB := { boundTcb with priority := newPri }
                    let stWithTcb : SystemState := { stStored with
                      objects := stStored.objects.insert boundTid.toObjId (KernelObject.tcb boundTcb2) }
                    -- AK2-B follow-up: re-bucket in RunQueue to match new priority.
                    let effectivePri : SeLe4n.Priority := match boundTcb.pipBoost with
                      | none => newPri
                      | some boostPri => ⟨Nat.max priority boostPri.val⟩
                    -- WS-SM SM8.B (PR #861 review round 13, found by
                    -- `scripts/check_live_arm_per_core_routing.py`): re-bucket on the
                    -- bound thread's HOME core.  Keyed on `bootCoreId` this was a
                    -- silent no-op for a thread queued anywhere else, so the priority
                    -- moved while the run queue kept the old band — the same defect
                    -- rounds 10 and 12 found in `migrateRunQueueBucket`.
                    let boundHome := determineTargetCore stWithTcb boundTid
                    if boundTid ∈ (stWithTcb.scheduler.runQueueOnCore boundHome) then
                      let rqRemoved := (stWithTcb.scheduler.runQueueOnCore boundHome).remove boundTid
                      let rqInserted := rqRemoved.insert boundTid effectivePri
                      { stWithTcb with scheduler :=
                        stWithTcb.scheduler.setRunQueueOnCore boundHome rqInserted }
                    else stWithTcb
                -- R5.G (DEEP-SCH-06): Domain propagation. The
                -- `boundThreadDomainConsistent` invariant in
                -- `Scheduler/Invariant.lean:847` requires that a bound
                -- thread's `tcb.domain` equal its SchedContext's
                -- `sc.domain`. `schedContextConfigure` rewrites
                -- `sc.domain := ⟨domain⟩`, so without propagating that
                -- write into the bound TCB's `domain` field the
                -- invariant would drift on every reconfigure that
                -- changes the domain.  Pre-R5 this propagation was
                -- missing — the invariant was implicitly maintained
                -- only by the AE3-A bind-time check, leaving
                -- `schedContextConfigure` as a silent invariant-
                -- violation path.
                --
                -- The post-state `stProp` may already have written
                -- `boundTcb2 := { boundTcb with priority := newPri }`
                -- into the objects table (when `priority` differs);
                -- in that case we read the latest TCB and update
                -- `domain` on it; otherwise we update the original
                -- `boundTcb`.
                let stFinal : SystemState :=
                  match stProp.getTcb? boundTid with
                  | some currentTcb =>
                    if currentTcb.domain.val = domain then stProp
                    else
                      let newDom : SeLe4n.DomainId := ⟨domain⟩
                      let currentTcb2 : TCB := { currentTcb with domain := newDom }
                      { stProp with objects :=
                        stProp.objects.insert boundTid.toObjId (KernelObject.tcb currentTcb2) }
                  | none => stProp  -- bound TCB vanished mid-op: leave as-is (consistent with priority block)
                .ok ((), stFinal)
              | none => .ok ((), stStored)  -- bound thread's TCB missing: leave as-is
        else
          .error .resourceExhausted
      | none => .error .objectNotFound

-- ============================================================================
-- Z5-G1/G2/G3: schedContextBind
-- ============================================================================

/-- Z5-G1/G2/G3: Bind a thread to a SchedContext.
1. Precondition: SchedContext has no bound thread, TCB is unbound
2. Set bidirectional binding (sc.boundThread, tcb.schedContextBinding)
3. Write both updated objects to store
4. If thread is in RunQueue, remove and re-insert at SchedContext priority
   to maintain `effectiveParamsMatchRunQueue` invariant

**AL8 (WS-AL / AK7-E.cascade)**: `scId` is `ValidObjId`, `threadId` is
`ValidThreadId` for compile-time sentinel rejection on BOTH IDs. -/
def schedContextBind (vScId : ValidObjId) (vThreadId : ValidThreadId) : Kernel Unit :=
  fun st =>
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration. Both
    -- the original `_ => .error .objectNotFound` arms collapsed
    -- wrong-variant and absent into the same error code, so migrating to
    -- `none => .error .objectNotFound` is semantics-preserving.
    match st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
    | some sc =>
      -- Z5-G1: Precondition check — SchedContext must not already have a bound thread
      if sc.boundThread.isSome then .error .illegalState
      else
        match st.getTcb? vThreadId.val with
        | some tcb =>
          -- AE3-A/U-11: Domain consistency check — reject cross-domain binding.
          -- The domain filter (chooseBestRunnableInDomainEffective) uses tcb.domain
          -- but effective priority resolves from sc.domain. Mismatched domains would
          -- cause a thread to pass the domain filter by TCB domain but be prioritized
          -- by SchedContext domain.
          if tcb.domain != sc.domain then .error .invalidArgument
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
            -- This establishes `tcb.priority = sc.priority` at bind time,
            -- aligning the base priority component that `schedulerPriorityMatch`
            -- and `effectiveParamsMatchRunQueue` each read. Without this, the
            -- two invariants jointly force `tcb.priority = sc.priority` in the
            -- extended bundle but no operation ever establishes the equality.
            -- Matches seL4 MCS where bind transfers scheduling authority from
            -- the TCB to its bound SchedContext.
            let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
            let updatedSc := { sc with boundThread := some vThreadId.val }
            let updatedTcb := { tcb with
              schedContextBinding := SchedContextBinding.bound scIdTyped,
              priority := sc.priority }
            -- Write both updated objects
            let st1 := { st with objects := st.objects.insert vScId.val (KernelObject.schedContext updatedSc) }
            let st2 := { st1 with objects := st1.objects.insert vThreadId.val.toObjId (KernelObject.tcb updatedTcb) }
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
            let bindHome := determineTargetCore st2 vThreadId.val
            let st3 := if vThreadId.val ∈ (st2.scheduler.runQueueOnCore bindHome) then
              let rqRemoved := (st2.scheduler.runQueueOnCore bindHome).remove vThreadId.val
              let rqInserted := rqRemoved.insert vThreadId.val (resolveInsertPriority st2 vThreadId.val sc)
              { st2 with scheduler := st2.scheduler.setRunQueueOnCore bindHome rqInserted }
            else st2
            -- S-05/PERF-O1: Add thread to per-SchedContext thread index
            let st4 := { st3 with scThreadIndex :=
              (scThreadIndexAdd st3.scThreadIndex scIdTyped vThreadId.val) }
            .ok ((), st4)
          | _ => .error .illegalState
        | none => .error .objectNotFound
    | none => .error .objectNotFound

-- ============================================================================
-- Z5-H1/H2/H3: schedContextUnbind
-- ============================================================================

/-- Z5-H1/H2/H3: Unbind a thread from a SchedContext.
1. Verify the SchedContext has a bound thread
2. (H1) If bound thread is the current thread, clear current to trigger
   rescheduling — prevents unbinding the running thread without preemption
3. (H2) If thread is in RunQueue, remove it (it will be re-enqueued at
   legacy TCB priority by the next schedule call if still runnable)
4. Clear both sides of the bidirectional binding
5. (H3) Remove SchedContext from replenish queue

**AL8 (WS-AL / AK7-E.cascade)**: `scId` is `ValidObjId` for compile-time
sentinel rejection. -/
def schedContextUnbind (vScId : ValidObjId) : Kernel Unit :=
  fun st =>
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration. The
    -- original `_ => .error .objectNotFound` arm collapsed wrong-variant
    -- and absent into the same error code, so migration is
    -- semantics-preserving.
    match st.getSchedContext? (SchedContextId.ofObjId vScId.val) with
    | some sc =>
      match sc.boundThread with
      | none => .error .illegalState
      | some tid =>
        match st.getTcb? tid with
        | some tcb =>
          -- Z5-H1: Preemption guard — if bound thread is current, clear current
          -- to force rescheduling. Under dequeue-on-dispatch, the current thread
          -- is not in the RunQueue, so clearing current is sufficient.
          -- WS-SM SM8.B (review round 13): the unbound thread's HOME core.  Keyed
          -- on `bootCoreId` the preemption guard never fired for a thread current
          -- on a secondary core, which kept running at its now-revoked SC priority.
          let unbindHome := determineTargetCore st tid
          let wasCurrent := (st.scheduler.currentOnCore unbindHome) == some tid
          let st0 := if wasCurrent then
            { st with scheduler := st.scheduler.setCurrentOnCore unbindHome none }
          else st
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
          let updatedTcb := { tcb with schedContextBinding := SchedContextBinding.unbound }
          let legacyPrio := effectiveRunQueuePriority updatedTcb
          let homeQueue := st0.scheduler.runQueueOnCore unbindHome
          let rebucketed := (homeQueue.remove tid).insert tid legacyPrio
          let st1 :=
            if tid ∈ homeQueue then
              { st0 with scheduler := st0.scheduler.setRunQueueOnCore unbindHome rebucketed }
            else if wasCurrent then
              { st0 with scheduler := st0.scheduler.setRunQueueOnCore unbindHome rebucketed }
            else st0
          -- Z5-H2 cont: Clear both sides of the binding
          let updatedSc := { sc with boundThread := none, isActive := false }
          let st2 := { st1 with objects := st1.objects.insert vScId.val (KernelObject.schedContext updatedSc) }
          let st3 := { st2 with objects := st2.objects.insert tid.toObjId (KernelObject.tcb updatedTcb) }
          -- Z5-H3: Remove SchedContext from replenish queue.
          -- WS-SM SM8.B (PR #861 review round 17): on `unbindHome`, the same
          -- core this operation already re-buckets the run queue on.  The
          -- run-queue side was routed per-core in round 13 and the replenish
          -- side was missed, so an unbind left the SC's eligibility entry
          -- queued on its home core with nothing bound to consume it.
          let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
          let st4 := purgeReplenishmentOnCore st3 unbindHome scIdTyped
          -- S-05/PERF-O1: Remove thread from per-SchedContext thread index
          let st5 := { st4 with scThreadIndex :=
            (scThreadIndexRemove st4.scThreadIndex scIdTyped tid) }
          .ok ((), st5)
        -- Bound thread's TCB not found — clear SC side anyway
        | none =>
          let updatedSc := { sc with boundThread := none, isActive := false }
          let st1 := { st with objects := st.objects.insert vScId.val (KernelObject.schedContext updatedSc) }
          -- WS-SM SM8.B (PR #861 review round 17): this arm is reached when the
          -- bound TCB is **already gone from the store**, so there is no
          -- `cpuAffinity` left to read and no home core to name — a
          -- `determineTargetCore` here would resolve to `bootCoreId` and
          -- reinstate exactly the boot-pinning being fixed.  Sweep instead, as
          -- the destroy path does for run queues.
          let scIdTyped : SchedContextId := ⟨vScId.val.toNat⟩
          let st2 := purgeReplenishmentFromAllCores st1 scIdTyped
          -- S-05/PERF-O1: Remove stale index entry even when TCB is missing
          let st3 := { st2 with scThreadIndex :=
            (scThreadIndexRemove st2.scThreadIndex scIdTyped tid) }
          .ok ((), st3)
    | none => .error .objectNotFound

-- ============================================================================
-- Z5-I1/I2: schedContextYieldTo (kernel-internal)
-- ============================================================================

/-- Z5-I1/I2: Transfer budget from one SchedContext to another.
Kernel-internal helper for hierarchical scheduling. Not a userspace syscall.
Transfers `budgetRemaining` from source to target, capped at target's
configured `budget`. If the target's bound thread was budget-starved
(budget was 0, now > 0), enqueue it in the RunQueue.

AF4-G (AF-30, AF-47): `schedContextYieldTo` is a KERNEL-INTERNAL helper,
not a syscall entry point. No capability check is performed here because
this function operates below the capability layer — callers are responsible
for validating access rights before invoking. It is a pure function
(returns `SystemState`, not monadic) because the yield operation has a
well-defined fallback for every input: pattern-match failures on missing
or non-SchedContext objects return `st` unchanged (identity fallback),
and budget transfer is always well-defined (capped at target's configured
budget via `min`). Cross-subsystem invariant preservation is proven by
`schedContextYieldTo_crossSubsystemInvariant_bridge` in CrossSubsystem.lean. -/
def schedContextYieldTo (st : SystemState) (fromScId targetScId : SchedContextId)
    : SystemState :=
  -- AK6-D (SC-M03): Self-yield guard. A yield to oneself is a no-op in any
  -- defensible semantics, but the naive implementation zeros the source
  -- SchedContext and then re-writes the target — when the two are the same
  -- object the final `HashMap.insert` ordering decides the stored state
  -- (`budgetRemaining := 0` wins with the current sequencing). Reject
  -- self-transfer by returning the state unchanged. `schedContextYieldTo`
  -- returns `SystemState` (not `Except`) because all failure paths are
  -- kernel-internal identity fallbacks; self-yield joins that family.
  if fromScId == targetScId then st else
  -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
  match st.getSchedContext? fromScId with
  | some fromSc =>
    match st.getSchedContext? targetScId with
    | some targetSc =>
      -- Z5-I1: Transfer budget from source to target
      let transferAmount := fromSc.budgetRemaining.val
      let newTargetBudget := min (targetSc.budgetRemaining.val + transferAmount) targetSc.budget.val
      let wasBudgetStarved := targetSc.budgetRemaining.val == 0
      let updatedFrom := { fromSc with budgetRemaining := Budget.zero, isActive := false }
      let updatedTarget := { targetSc with
        budgetRemaining := ⟨newTargetBudget⟩
        isActive := newTargetBudget > 0 }
      let st1 := { st with objects := st.objects.insert fromScId.toObjId (KernelObject.schedContext updatedFrom) }
      let st2 := { st1 with objects := st1.objects.insert targetScId.toObjId (KernelObject.schedContext updatedTarget) }
      -- Z5-I2: If target's bound thread was budget-starved and now has budget,
      -- enqueue it in RunQueue so it becomes schedulable again.
      if wasBudgetStarved && newTargetBudget > 0 then
        match targetSc.boundThread with
        | some tid =>
          -- AG1-A: Use effective priority (base + PIP boost) for RunQueue insertion
          -- WS-SM SM8.B (review round 13): re-enqueue on the thread's HOME core.
          let refillHome := determineTargetCore st2 tid
          if tid ∉ (st2.scheduler.runQueueOnCore refillHome) && (st2.scheduler.currentOnCore refillHome) != some tid then
            { st2 with scheduler := st2.scheduler.setRunQueueOnCore refillHome ((st2.scheduler.runQueueOnCore refillHome).insert tid (resolveInsertPriority st2 tid targetSc)) }
          else st2
        | none => st2
      else st2
    | none => st
  | none => st

end SeLe4n.Kernel.SchedContextOps
