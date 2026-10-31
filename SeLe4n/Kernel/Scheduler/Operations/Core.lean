-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.SchedContext.Budget
import SeLe4n.Kernel.IPC.Operations.Timeout
import SeLe4n.Kernel.Scheduler.Operations.ReschedulePending
import SeLe4n.Kernel.SchedContext.ReleaseLinks

/-!
# Scheduler Core Operations — AK2 closure status

**Addressed in this workstream (v0.29.2):**
- AK2-A + AK2-B (S-H03 + S-H04) via Option B — three-part fix:
  1. **Bind propagation:** `schedContextBind` sets
     `tcb.priority := sc.priority` on the bound TCB
     (`SchedContext/Operations.lean`), establishing the propagation
     invariant at the moment of binding. The existing Z5-G3 RunQueue
     remove+re-insert at `resolveInsertPriority` keeps the RunQueue bucket
     in sync with the new priority.
  2. **Configure propagation + re-bucketing:** `schedContextConfigure`
     additionally, when the SchedContext is currently bound and the
     reconfigure changes `sc.priority`, (a) updates the bound TCB's
     `priority` field to match, and (b) remove+re-inserts the bound thread
     in the RunQueue at `max(new priority, pipBoost)` if it was present.
     Without the re-bucketing the thread would sit in the old priority
     bucket while `tcb.priority` was updated — a latent priority-inversion
     vector that an earlier draft of this work introduced.
  3. **Consumption sites unchanged:** the four production re-enqueue
     sites (`handleYield`, `timerTick`, `timerTickBudget` unbound,
     `switchDomain`) continue to use `tcb.boostedPriority`, eliminating
     the priority-inversion vector.

     *WS-RR (`v0.35.133`) narrows what that costs.*  This point used to
     read that `tcb.boostedPriority` equals the
     `(resolveEffectivePrioDeadline st tcb).1` selection consults **under
     the propagation invariant**, and that `schedulerPriorityMatch`
     (TCB-based) and `effectiveParamsMatchRunQueue` (SC-based) agree
     without invariant fusion.  With `TCB.priority` the base's one home
     both readings are unconditional: the equality is
     `resolveEffectivePrioDeadline_fst_eq_threadBasePriority` composed with
     `threadBasePriority_eq`, which assumes nothing, and neither predicate
     is SC-based any more — `effectiveParamsMatchRunQueue` reads no
     SchedContext at all, so the two differ only in the PIP boost.
- AK2-D (S-M02): `timeoutBlockedThreads` errors surfaced via
  `SchedulerState.lastTimeoutErrors` diagnostic field, cleared at each
  `timerTickWithBudget` entry.
- AK2-E (S-M03): CBS admission ceiling-round in `Bandwidth.utilization`.
- AK2-F (S-M04): `ReplenishQueue.insertSorted` strict `<` comparator
  enforces FIFO within equal-eligibility ties.
- AK2-G (S-M05): `schedContextConfigure` purges stale replenishQueue
  entries before storing the reconfigured SchedContext.
- AK2-I (S-M07): `switchDomain` impossible fallback emits
  `.schedulerInvariantViolation` instead of silently returning unchanged
  state; proven unreachable under `domainScheduleEntriesPositive`.
- AK2-J (S-M08): `migrateRunQueueBucket` fallback preserves RunQueue
  priority via `max(newPriority, threadPriority[tid]?)`.
- AK2-L (S-L13..S-L18): LOW-tier scheduler batch documentation inline.

**Deferred to AK2.5 (escape valve §20.3 of WS-AK plan):**
- AK2-C (S-M01): `blockingChain` fuel-exhaustion → `Except`. Return-type
  change cascades to `Propagate.lean`, `BoundedInversion.lean`, `Boot.lean`,
  `CrossSubsystem.lean`.
- AK2-H (S-M06): route `schedule`/`scheduleEffective`/`switchDomain` through
  `saveOutgoingContextChecked`/`restoreIncomingContextChecked`. Under
  `currentThreadValid` the unchecked variants are provably safe via
  `saveOutgoingContext_always_succeeds_under_currentThreadValid` (AI3-C),
  giving equivalent formal assurance. Runtime assertion hardening deferred.
- AK2-K (S-H01/S-H02): WCRT proof-schema closure. Per escape valve, defer
  K.1/K.2/K.3 to AK2.5 sub-workstream; K.4 (documentation of
  `eventuallyExits` residual hypothesis) captured in
  `docs/spec/SELE4N_SPEC.md` §5.7.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId CoreId SgiKind)

/-- WS-ZA ZA6.3: **a release-queue edit is a run-queue stage** — it writes
contexts' release fields and the release queues alone, so every thread's TCB,
every slot's back-links, the run queues, their ends and every current slot are
kept; the release queues stay refined by `hR` and the refill state sound by
`hF`. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueFrameStage.of_releaseOnlyWrite
    {P : SchedContextId → Prop} {st st' : SystemState} (hW : st'.releaseOnlyWrite st)
    (hA : st'.objectsAgreeOffReleaseLinks st) (hI : st.objects.invExt → st'.objects.invExt)
    (hR : st.objects.invExt → st.releaseQueueRefined → st'.releaseQueueRefined)
    (hF : ∀ S, (∀ x, P x → S x) → st.objects.invExt → st.releaseQueueRefined →
      st.refillsSoundExcept S → st'.refillsSoundExcept S) :
    SystemState.RunQueueFrameStage P st st' := by
  have hS := hW.2
  refine SystemState.RunQueueFrameStage.of_tcbFrame (fun t => hA.getTcb? t) hA.tableBackLinks hI
    ?_ ?_ ?_ ?_ hR hF (fun _ => .of_agreeOffReleaseLinks hA)
  · rw [hS]
  · rw [hS]
  · rw [hS]
  · rw [hW.1]; rfl

/-- ...with the refill state carried off every set by `hF`. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.of_releaseOnlyWrite
    {st st' : SystemState} (hW : st'.releaseOnlyWrite st)
    (hA : st'.objectsAgreeOffReleaseLinks st) (hI : st.objects.invExt → st'.objects.invExt)
    (hR : st.objects.invExt → st.releaseQueueRefined → st'.releaseQueueRefined)
    (hF : ∀ S, st.objects.invExt → st.releaseQueueRefined → st.refillsSoundExcept S →
      st'.refillsSoundExcept S) :
    SystemState.RunQueueStage st st' := by
  have hS := hW.2
  exact SystemState.RunQueueStage.of_tcbFrame (fun t => hA.getTcb? t) hA.tableBackLinks hI
    (by rw [hS]) (by rw [hS]) (by rw [hS]) (by rw [hW.1]; rfl) hR hF
    (fun _ => .of_agreeOffReleaseLinks hA)

-- WS-H12c: Frame lemmas — context save/restore do not affect scheduler state.

@[simp] theorem saveOutgoingContext_scheduler (st : SystemState) :
    (saveOutgoingContext st).scheduler = st.scheduler := by
  simp only [saveOutgoingContext]
  cases (st.scheduler.currentOnCore bootCoreId) with
  | none => rfl
  | some outTid => exact SystemState.updateTcb_scheduler _ _ _

@[simp] theorem restoreIncomingContext_scheduler (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).scheduler = st.scheduler := by
  simp only [restoreIncomingContext]
  cases h : st.getTcb? tid with
  | none => simp_all
  | some _ => simp_all

@[simp] theorem restoreIncomingContext_objects (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).objects = st.objects := by
  simp only [restoreIncomingContext]
  cases h : st.getTcb? tid with
  | none => simp_all
  | some _ => simp_all

/-- `saveOutgoingContext` preserves the existence of a TCB at any object ID.
If `st.objects[oid]? = some (.tcb tcb)`, then there exists a TCB at `oid`
in `(saveOutgoingContext st).objects` as well. -/
theorem saveOutgoingContext_preserves_tcb
    (st : SystemState) (oid : SeLe4n.ObjId) (tcb : TCB)
    (h : st.objects[oid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt) :
    ∃ tcb', (saveOutgoingContext st).objects[oid]? = some (.tcb tcb') := by
  unfold saveOutgoingContext
  cases hCur : (st.scheduler.currentOnCore bootCoreId) with
  | none => exact ⟨tcb, h⟩
  | some outTid =>
      dsimp only
      cases hOut : st.getTcb? outTid with
      | none => rw [SystemState.updateTcb_eq_self_of_none hOut]; exact ⟨tcb, h⟩
      | some outTcb =>
          rw [SystemState.updateTcb_eq_of_some hOut]
          dsimp only
          simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
          by_cases hEq : outTid.toObjId == oid
          · simp [hEq]
          · simp [hEq]; exact ⟨tcb, h⟩
/-- `saveOutgoingContext` preserves all TCB fields except `registerContext`. -/
theorem saveOutgoingContext_tcb_fields
    (st : SystemState) (oid : SeLe4n.ObjId) (tcb : TCB)
    (h : st.objects[oid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt) :
    ∃ tcb', (saveOutgoingContext st).objects[oid]? = some (.tcb tcb') ∧
      tcb'.domain = tcb.domain ∧
      tcb'.priority = tcb.priority ∧
      tcb'.deadline = tcb.deadline ∧
      tcb'.timeSlice = tcb.timeSlice ∧
      tcb'.pipBoost = tcb.pipBoost ∧
      tcb'.schedContextBinding = tcb.schedContextBinding := by
  unfold saveOutgoingContext
  cases hCur : (st.scheduler.currentOnCore bootCoreId) with
  | none => exact ⟨tcb, h, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | some outTid =>
      dsimp only
      cases hOut : st.getTcb? outTid with
      | none => rw [SystemState.updateTcb_eq_self_of_none hOut]; exact ⟨tcb, h, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some outTcb =>
          rw [SystemState.updateTcb_eq_of_some hOut]
          dsimp only
          simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
          by_cases hEq : outTid.toObjId == oid
          · simp only [hEq, ite_true]
            have hEq' := beq_iff_eq.mp hEq
            subst hEq'
            rw [(SystemState.getTcb?_eq_some_iff st outTid outTcb).mp hOut] at h; cases h
            exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · simp [hEq]; exact ⟨tcb, h, rfl, rfl, rfl, rfl, rfl, rfl⟩
/-- When `st.objects[oid]?` is not a TCB (i.e., `none` or a non-TCB object),
`saveOutgoingContext` preserves the lookup unchanged. This is because the only
insert targets `outTid.toObjId` where a TCB exists — if `oid` had no TCB, it
cannot be that key. -/
theorem saveOutgoingContext_preserves_non_tcb_lookup
    (st : SystemState) (oid : SeLe4n.ObjId)
    (hNonTcb : ∀ tcb, st.objects[oid]? ≠ some (.tcb tcb))
    (hObjInv : st.objects.invExt) :
    (saveOutgoingContext st).objects[oid]? = st.objects[oid]? := by
  simp only [saveOutgoingContext]
  cases hCur : (st.scheduler.currentOnCore bootCoreId) with
  | none => rfl
  | some outTid =>
      dsimp only
      cases hOut : st.getTcb? outTid with
      | none => rw [SystemState.updateTcb_eq_self_of_none hOut]
      | some outTcb =>
          rw [SystemState.updateTcb_eq_of_some hOut]
          dsimp only
          simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
          have hNe : ¬(outTid.toObjId == oid) := by
            intro hEq
            have hEq' := beq_iff_eq.mp hEq
            subst hEq'
            exact hNonTcb outTcb ((SystemState.getTcb?_eq_some_iff st outTid outTcb).mp hOut)
          simp [hNe]
/-- `saveOutgoingContext` preserves `timeSlicePositive`. The context save only
changes `registerContext` on the outgoing TCB — no scheduler or time-slice
field is modified. -/
theorem saveOutgoingContext_preserves_timeSlicePositive
    (st : SystemState) (hInv : timeSlicePositive st)
    (hObjInv : st.objects.invExt) :
    timeSlicePositive (saveOutgoingContext st) := by
  intro tid hMem
  have hSched : (saveOutgoingContext st).scheduler = st.scheduler := saveOutgoingContext_scheduler st
  have hMemOrig : tid ∈ st.scheduler.runnable := by rwa [← hSched]
  have hOrig := hInv tid hMemOrig
  unfold saveOutgoingContext
  cases hCur : (st.scheduler.currentOnCore bootCoreId) with
  | none => exact hOrig
  | some outTid =>
      dsimp only
      cases hOut : st.getTcb? outTid with
      | none => rw [SystemState.updateTcb_eq_self_of_none hOut]; exact hOrig
      | some outTcb =>
          rw [SystemState.updateTcb_eq_of_some hOut]
          dsimp only
          simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
          by_cases hEq : outTid.toObjId == tid.toObjId
          · -- Same key: inserted TCB has same timeSlice as original
            simp [hEq]
            have hEq' := beq_iff_eq.mp hEq
            -- `hOut` is the accessor equation; the key rewrite is about the
            -- store subscript, so it crosses first.
            have hOutRaw := (SystemState.getTcb?_eq_some_iff st outTid outTcb).mp hOut
            rw [hEq'] at hOutRaw; simp [hOutRaw] at hOrig; exact hOrig
          · simp [hEq]; exact hOrig
/-- `saveOutgoingContext` preserves `objects.invExt`. The context save
inserts a TCB at an existing key, which preserves the Robin Hood invariant. -/
theorem saveOutgoingContext_preserves_objects_invExt
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (saveOutgoingContext st).objects.invExt := by
  unfold saveOutgoingContext
  cases hCur : (st.scheduler.currentOnCore bootCoreId) with
  | none => exact hObjInv
  | some outTid =>
      dsimp only
      exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hObjInv
/-- `restoreIncomingContext` preserves `timeSlicePositive`. The context restore
only changes `machine.regs` — objects and scheduler state are unchanged. -/
private theorem restoreIncomingContext_preserves_timeSlicePositive
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : timeSlicePositive st) :
    timeSlicePositive (restoreIncomingContext st tid) := by
  intro t hMem
  have hSched : (restoreIncomingContext st tid).scheduler = st.scheduler := restoreIncomingContext_scheduler st tid
  have hMemOrig : t ∈ st.scheduler.runnable := by rwa [← hSched]
  have hOrig := hInv t hMemOrig
  simp only [restoreIncomingContext_objects]; exact hOrig

/-- WS-H12c: After `restoreIncomingContext st tid`, when `st.objects[tid.toObjId]?`
is a TCB, the machine register file equals that TCB's `registerContext`. -/
theorem restoreIncomingContext_establishes_context
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb)) :
    (restoreIncomingContext st tid).machine.regs = tcb.registerContext := by
  simp only [restoreIncomingContext, (SystemState.getTcb?_eq_some_iff st tid tcb).mpr hTcb,
    MachineState.regs_setRegsOnCore_bootCore]

/-- WS-H12c: `restoreIncomingContext` does not change the machine state when
the given thread ID does not correspond to a TCB in the object store. -/
@[simp] theorem restoreIncomingContext_machine_no_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (h : ∀ tcb, st.objects[tid.toObjId]? ≠ some (.tcb tcb)) :
    (restoreIncomingContext st tid).machine = st.machine := by
  unfold restoreIncomingContext
  cases hObj : st.getTcb? tid with
  | none => rfl
  | some t => exact absurd ((SystemState.getTcb?_eq_some_iff st tid t).mp hObj) (h t)
/-- WS-H12b/H-04 + WS-H12c/H-03: Scheduler step with dequeue-on-dispatch and
inline context switch semantics.

Failure modes are explicit:
- malformed runnable entries (non-TCB object IDs) surface as `schedulerInvariantViolation`,
- selecting a thread not present in runnable also surfaces as `schedulerInvariantViolation`.

**Dequeue-on-dispatch (H-04):** After validation, the selected thread is
removed from the run queue before being set as current. This matches seL4's
`switchToThread` → `tcbSchedDequeue` semantics. The dispatched thread is
re-enqueued only on preemption (`timerTick`), yield (`handleYield`), or
domain switch (`switchDomain`).

**Inline context switch (H-03):** The context switch is performed directly
inside `schedule` rather than as separate save/restore helpers. This matches
seL4's `switchToThread` design where the context switch is an integral part
of thread dispatch. The transition:
1. Save outgoing: if `current = some outTid`, store `machine.regs` into
   the outgoing TCB's `registerContext`.
2. Dequeue incoming thread from the run queue.
3. Restore incoming: load `inTcb.registerContext` into `machine.regs`.
4. Set `current` to the incoming thread.

This ensures `contextMatchesCurrent` (machine.regs = currentThread.registerContext)
is established atomically by `schedule` itself.

**Performance note:** Membership validation uses O(1) HashSet-backed
`tid ∈ (st'.scheduler.runQueueOnCore bootCoreId)`.

**U8-D/U-L26: Starvation and fairness:** This is a strict fixed-priority
preemptive scheduler matching seL4's classic scheduling model. Starvation
freedom is NOT a property of this scheduler — a continuously runnable
high-priority thread will indefinitely preempt lower-priority threads.
seL4 delegates starvation prevention to user-level policy (e.g., MCS
scheduling extensions, which are not yet modeled in seLe4n).

**V5-D/V5-E design note:** `schedule` uses the unchecked `saveOutgoingContext` /
`restoreIncomingContext` internally because all 20+ preservation proofs
(`schedule_preserves_schedulerInvariantBundle`, etc.) unfold these functions by
name. The checked variants (`saveOutgoingContextChecked` / `restoreIncomingContextChecked`)
return `SystemState × Bool` for defense-in-depth at API boundaries; equivalence
theorems (`saveOutgoingContextChecked_fst_eq`, `restoreIncomingContextChecked_fst_eq`)
guarantee the state component is identical. Under `currentThreadValid`, the
`false` branches are unreachable.

**AN5-B (SCH-M04) — operation/wrapper boundary annotation.** The four
primary scheduler operations (`schedule`, `handleYield`, `timerTick`,
`switchDomain`, `scheduleDomain`) are pure transitions. The context
save/restore wrappers (`saveOutgoingContext`, `restoreIncomingContext`,
and their checked variants) are the proof harness — they carry the
dequeue-on-dispatch and `contextMatchesCurrent` frame lemmas. The
formal split into `Operations.lean` (pure) and `Wrappers.lean` (proof
harness) is tracked alongside the Theme 4.7 Preservation.lean
decomposition (AN5-A): the child-module layout there naturally
accommodates a parallel split here without causing duplicate-import
churn. At 1002 LOC `Core.lean` remains well under the 2000-LOC Theme
4.7 ceiling. -/
noncomputable def schedule : Kernel Unit :=
  fun st =>
    match chooseThread st with
    | .error e => .error e
    | .ok (none, st') =>
        -- WS-H12c: save outgoing context before going idle
        let stSaved := saveOutgoingContext st'
        setCurrentThread none stSaved
    | .ok (some tid, st') =>
        match st'.getTcb? tid with
        | some tcb =>
            -- AF1-G: Domain check uses static `tcb.domain`, safe under
            -- `boundThreadDomainConsistent` (AE3-A: sc.domain = tcb.domain).
            if tid ∈ (st'.scheduler.runQueueOnCore bootCoreId) ∧ tcb.domain = (st'.scheduler.activeDomainOnCore bootCoreId) then
              -- WS-H12c: save outgoing thread's register context
              let stSaved := saveOutgoingContext st'
              -- WS-H12b: dequeue before dispatch (seL4 tcbSchedDequeue)
              let stDequeued := { stSaved with scheduler := stSaved.scheduler.setRunQueueOnCore bootCoreId ((stSaved.scheduler.runQueueOnCore bootCoreId).remove tid) }
              -- WS-H12c: restore incoming thread's register context
              let stRestored := restoreIncomingContext stDequeued tid
              setCurrentThread (some tid) stRestored
            else
              .error .schedulerInvariantViolation
        | none => .error .schedulerInvariantViolation

/-- WS-H12b/H-04 + WS-H12c/H-03: Yield semantics with dequeue-on-dispatch.

Under dequeue-on-dispatch, the current thread is NOT in the run queue.
Yield re-enqueues the current thread at the back of its priority bucket
(insert + rotateToBack), then calls schedule to select a new thread.

Context save/restore is handled inline by `schedule`: the outgoing thread's
registers are saved to its TCB and the incoming thread's registers are
restored from its TCB, establishing `contextMatchesCurrent` atomically.

This mirrors seL4's `handleYield` → `tcbSchedDequeue` + `tcbSchedAppend`
(append = enqueue at tail) → `rescheduleRequired` → `schedule()`. -/
/-
AK2-L (S-L13..S-L18) — Scheduler LOW-tier documentation batch.

- S-L13 `handleYield` error semantics: the `none => .invalidArgument` arm
  below reports a caller-side precondition violation (no current thread).
  Syscall dispatch never reaches yield without a current thread under
  `currentThreadValid`, so the arm is unreachable in production; the code
  returns `.invalidArgument` (not `.schedulerInvariantViolation`) so that a
  misbehaving userspace caller receives an ABI-stable "bad call" signal
  rather than a kernel-internal invariant error.
- S-L14 `getCurrentPriority` silent fallback: addressed in AE3 by routing
  through `resolveEffectivePrioDeadline`; the defensive `tcb.priority`
  fallback is formally unreachable under `boundThreadDomainConsistent` +
  `schedContextBindingConsistent` (see `Selection.lean:314–322`).
- S-L15 `oid.toNat→ThreadId` direct cast: prefer `ThreadId.ofObjId`
  which carries sentinel handling. Existing sites are in `Lifecycle/` and
  only dispatch at verified object boundaries; any future decode path
  crossing module boundaries must use the checked constructor.
- S-L16 `isBetterCandidate_transitive` proof brittleness: the transitivity
  lemma is discharged case-by-case on priority/deadline ordering and is
  stable under `Nat`-`DecidableLinearOrder`; refactor to a structural
  tuple-compare helper is tracked for AK2.5.
- S-L17 `⟨Nat.max …⟩` bypasses `Priority` validity: the PIP-boost
  constructor in `migrateRunQueueBucket` (fixed by AK2-J) and in
  `resolveEffectivePrioDeadline` directly builds a `Priority` from
  `Nat.max`. The `Priority` wrapper carries no validity predicate beyond
  `Nat`, so the construction is sound; future tightening (e.g., a
  `Priority.ofNat?` with clamp to `numPriorities - 1`) is tracked for AK7.
- S-L18 `runQueueUnique` flat-list only: the predicate asserts `Nodup` on
  the projected flat list; per-bucket uniqueness is implied by
  `RunQueue.wellFormed` (distinct priority per tid ⇒ a thread appears in
  exactly one bucket). A dedicated per-bucket lemma is tracked for AK2.5
  alongside the fused priority-match predicate (AK2-B).
-/
noncomputable def handleYield : Kernel Unit :=
  fun st =>
    match (st.scheduler.currentOnCore bootCoreId) with
    | none =>
        -- V5-F (M-DEF-6) / S-L13: Return `.invalidArgument` when no thread is
        -- current instead of falling through to `schedule`. Yielding requires
        -- a current thread to re-enqueue. Without one, the yield is a no-op
        -- error — callers should check `current` before invoking yield.
        -- `.invalidArgument` (rather than `.schedulerInvariantViolation`)
        -- gives userspace a stable "bad syscall" signal.
        .error .invalidArgument
    | some tid =>
        match st.getTcb? tid with
        | some tcb =>
            -- AI3-A (M-04) / AK2-A (S-H03): Re-enqueue at
            -- `tcb.boostedPriority` (base + PIP boost). For
            -- SchedContext-bound threads, the AK2-B Option B propagation
            -- invariant (`tcb.priority = sc.priority` enforced by
            -- `schedContextBind` and `schedContextConfigure`) guarantees this
            -- equals `(resolveEffectivePrioDeadline st tcb).1` read by
            -- selection. `schedulerPriorityMatch` therefore holds post-insert.
            let rq' := ((st.scheduler.runQueueOnCore bootCoreId).insert tid (tcb.boostedPriority)).rotateToBack tid
            let st' := { st with scheduler := st.scheduler.setRunQueueOnCore bootCoreId rq' }
            schedule st'
        | none => .error .schedulerInvariantViolation

-- ============================================================================
-- M-04/WS-E6: Time-slice preemption
-- ============================================================================

-- `defaultTimeSlice : Nat := 5` stood here and is **deleted** at `v0.35.103`.
-- It was superseded by the per-instance `SchedulerState.configDefaultTimeSlice`
-- (AC2-C) and retained on a justification that named a consumer which does not
-- exist: *"for use in contexts where no `SchedulerState` is available (e.g.,
-- frozen operations)"*.  A `FrozenSystemState` carries a `FrozenSchedulerState`,
-- so `frozenTimerTick` reads `st.scheduler.configDefaultTimeSlice` like the live
-- tick below, and measurement put the constant's whole-tree reference count at
-- zero.  `frozenDefaultTimeSlice`, which carried the mirror-image false claim
-- (*"retained for backward compatibility in tests that reference this
-- constant"*, referenced by no test), went in the same cut.  A quantum is read
-- from `st.scheduler.configDefaultTimeSlice`; a Tier 3 negative refuses either
-- name coming back.

/-- WS-H12b/H-04 + WS-H12c/H-03: Handle a timer tick with dequeue-on-dispatch
and inline context switch semantics.

Behavior:
1. If no thread is current, advance the machine timer only.
2. If the current thread's time-slice has not expired (> 1 after decrement),
   decrement and advance the machine timer.
3. If the time-slice expires (≤ 1), reset it to `st.scheduler.configDefaultTimeSlice`,
   re-enqueue the current thread into the run queue, and reschedule.

Under dequeue-on-dispatch, the current thread is NOT in the run queue.
On preemption, we insert it back (seL4's `tcbSchedEnqueue(current)`)
before calling `schedule()`. Context save/restore is handled inline by
`schedule`: the outgoing thread's registers are saved to its TCB and
the incoming thread's registers are restored, establishing
`contextMatchesCurrent` atomically. -/
noncomputable def timerTick : Kernel Unit :=
  fun st =>
    match (st.scheduler.currentOnCore bootCoreId) with
    | none =>
        -- No current thread: just advance the timer
        .ok ((), { st with machine := tick st.machine })
    | some tid =>
        match st.getTcbWitnessed? tid with
        | some ⟨tcb, h⟩ =>
            if tcb.timeSlice ≤ 1 then
              -- Time-slice expired: reset, re-enqueue, reschedule
              -- AC2-C: uses the configurable `configDefaultTimeSlice` from scheduler
              -- state (its own default is 5). Preservation proofs carry an
              -- `hConfigTS` hypothesis requiring `configDefaultTimeSlice > 0`.
              let tcb' := { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }
              let st' := { st.rewriteObject tid.toObjId (.tcb tcb')
                             (SystemState.rewriteAdmissible_tcb h tcb') with
                           machine := tick st.machine }
              -- WS-H12b: re-enqueue current thread before schedule.
              -- AI3-A (M-04) / AK2-A (S-H03): Re-enqueue at
              -- `tcb.boostedPriority` (priority + PIP boost).
              -- The `tcb` value is bound PRE-mutation (before `st'`'s timeSlice
              -- update), and `TCB.boostedPriority` depends only on
              -- `tcb.priority` and `tcb.pipBoost` — both of which are unchanged
              -- across the timeSlice mutation. Under the AK2-B Option B
              -- propagation invariant this value equals the SC-aware priority
              -- used by selection (see Core.lean module docstring).
              let st'' := { st' with scheduler := st'.scheduler.setRunQueueOnCore bootCoreId (((st'.scheduler.runQueueOnCore bootCoreId).insert tid (tcb.boostedPriority))) }
              schedule st''
            else
              -- Time-slice not expired: decrement and continue
              let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
              .ok ((), { st.rewriteObject tid.toObjId (.tcb tcb')
                           (SystemState.rewriteAdmissible_tcb h tcb') with
                         machine := tick st.machine })
        | none => .error .schedulerInvariantViolation

-- ============================================================================
-- Z4-G: System-level replenishment processing
-- ============================================================================

/-- Z4-G1: Pop all due replenishment entries from the system replenish queue.
Returns the list of SchedContextIds that are due for replenishment and the
remaining queue. Wraps `ReplenishQueue.popDue` at the system level. -/
noncomputable def popDueReplenishments (st : SystemState) (now : Nat)
    : ReplenishQueue × List SeLe4n.SchedContextId :=
  (st.scheduler.replenishQueueOnCore bootCoreId).popDue now

/-- Z4-G2: Refill a single SchedContext's budget via CBS replenishment processing.
WS-ZA ZA6.4: the release of a used-up head (`SchedContext.releaseReadyHead`,
seL4-MCS's `refill_ready` head taken when the context is woken off its release
queue) and the CBS deadline rule, written back to the store through
`SystemState.updateSchedContext` (the in-place rewrite under the witnessed
lookup).  The release reads and writes the context's own fields, so no refill
list is built.  No-op if the SchedContext is not found. -/
def refillSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (now : Nat) : SystemState :=
  st.updateSchedContext scId fun sc =>
    cbsUpdateDeadline (sc.releaseReadyHead now) now true

/-- Z4-G3: Process all due replenishments and re-enqueue threads whose budget
was restored. Pops due entries from the replenish queue, refills each
SchedContext, and for any bound thread whose budget went from 0 to positive,
enqueues it in the RunQueue.

Z6-F: No timeout action needed during replenishment. Replenishment *restores*
budget, which is the opposite of timeout. Threads blocked on IPC whose
SchedContext is replenished should remain blocked — they now have budget
again. Only `timerTickBudget`'s budget-exhaustion branch (Z4-F3) triggers
`timeoutBlockedThreads`, ensuring that timeouts fire only when
`budgetRemaining = 0`. This guard is correct by construction: this function
never calls `timeoutBlockedThreads`. -/
noncomputable def processReplenishmentsDue (st : SystemState) (now : Nat) : SystemState :=
  let (remainingQueue, dueIds) := popDueReplenishments st now
  let st' := { st with scheduler := st.scheduler.setReplenishQueueOnCore bootCoreId remainingQueue }
  dueIds.foldl (fun acc scId =>
    let wasExhausted := match acc.getSchedContext? scId with
      | some sc => sc.budgetRemaining.isZero
      | none => false
    let refilled := refillSchedContext acc scId now
    -- If the SchedContext's bound thread was budget-exhausted and is now refilled,
    -- re-enqueue the thread into the RunQueue
    match refilled.getSchedContext? scId with
    | some sc =>
      if wasExhausted && sc.budgetRemaining.isPositive then
        match sc.boundThread with
        | some tid =>
          -- Only re-enqueue if the thread is not already current or in queue
          -- AG1-A: Use effective priority (base + PIP boost) for RunQueue insertion
          if tid ∈ (refilled.scheduler.runQueueOnCore bootCoreId) then refilled
          else if (refilled.scheduler.currentOnCore bootCoreId) == some tid then refilled
          else { refilled with scheduler := refilled.scheduler.setRunQueueOnCore bootCoreId (((refilled.scheduler.runQueueOnCore bootCoreId).insert tid (resolveInsertPriority refilled tid sc))) }
        | none => refilled
      else refilled
    | none => refilled
  ) st'

-- ============================================================================
-- Z6-E: Timeout blocked threads on budget expiry
-- ============================================================================

/-- Z6-E: Helper to determine if a TCB's IPC state is a blocking state
that should be timed out, and returns the endpoint ID and queue type.

WS-SM SM5.D.5: de-privatized (was `private`) so the per-core timer-tick
preservation proofs (`timeoutBlockedThreads_preserves_objects_invExt`, which fold
over `tcbBlockingInfo`'s `Option` result) can `cases` on it as an opaque
`Option (ObjId × Bool)` rather than splitting it into `ipcState` constructor
cases. -/
def tcbBlockingInfo (tcb : TCB) : Option (SeLe4n.ObjId × Bool) :=
  match tcb.ipcState with
  | .blockedOnSend epId => some (epId, false)      -- sendQ
  | .blockedOnReceive epId => some (epId, true)     -- receiveQ
  | .blockedOnCall epId => some (epId, false)       -- sendQ (Call uses sendQ)
  | .blockedOnReply epId _ => some (epId, false)    -- not in queue but still blocked
  | _ => none

/-- The one timeout step of `timeoutBlockedThreads`: a thread blocked in IPC is
timed out of its endpoint, any other thread is left as it is.  A timeout wake is
target-aware (PR #880 round 8): it lands on the thread's home core, and a remote
home core's `.reschedule` SGI is accumulated for the caller to emit after its
state commit.  A refused timeout is collected rather than swallowed (AG1-B);
under `crossSubsystemInvariant` it is unreachable. -/
def timeoutBlockedThreadStep (execCore : CoreId)
    (acc : SystemState × List (SeLe4n.ThreadId × KernelError) × List (CoreId × SgiKind))
    (tid : SeLe4n.ThreadId) :
    SystemState × List (SeLe4n.ThreadId × KernelError) × List (CoreId × SgiKind) :=
  let (st', errs, sgis) := acc
  match st'.getTcb? tid with
  | some tcb =>
    match tcbBlockingInfo tcb with
    | some (epId, isReceiveQ) =>
      match timeoutThread epId isReceiveQ tid execCore st' with
      | .ok r => (r.1, errs, sgis ++ r.2.toList)
      | .error e => (st', errs ++ [(tid, e)], sgis)
    | none => (st', errs, sgis)  -- not blocked on IPC
  | none => (st', errs, sgis)

/-- The threads an exhausted context's timeout pass visits: the one thread the
context is bound to (`SchedContext.boundThread`, seL4's `sc->scTcb`), which a
donation moves to the server running on it, or none. -/
def schedContextTimeoutThreads (st : SystemState) (scId : SeLe4n.SchedContextId) :
    List SeLe4n.ThreadId :=
  match st.getSchedContext? scId with
  | some sc => sc.boundThread.toList
  | none => []

/-- Z6-E: Timeout the thread blocked on IPC whose SchedContext budget has been
exhausted.

When a SchedContext's budget reaches zero, the thread relying on it to bound
its IPC blocking time must be unblocked.  That thread is the context's bound
thread: a context names at most one thread (`SchedContext.boundThread`, seL4's
`sc->scTcb`), and a donation rebinds it to the server it lends to, so a
descheduled donor is never visited.  Reading the context replaces the
per-context thread index (`scThreadIndex`, retired in WS-ZA ZA5.2), which
held the same one thread in a list every bind consed into.

Note: threads in `blockedOnReply` are also timed out. In seL4 MCS, this
handles the case where a client's donated budget expires while the server
is running — the client is unblocked with a timeout error (Z6-E integration
with Z7 donation).

The definition matches on the context directly, so the pass builds no list;
`timeoutBlockedThreads_eq_fold` states it as the fold of
`timeoutBlockedThreadStep` over `schedContextTimeoutThreads`, the form proofs
reason about. -/
def timeoutBlockedThreads (st : SystemState) (scId : SeLe4n.SchedContextId)
    (execCore : CoreId)
    : SystemState × List (SeLe4n.ThreadId × KernelError) × List (CoreId × SgiKind) :=
  match st.getSchedContext? scId with
  | some sc =>
    match sc.boundThread with
    | some tid => timeoutBlockedThreadStep execCore (st, [], []) tid
    | none => (st, [], [])
  | none => (st, [], [])

/-- The timeout pass is the fold of its step over the context's threads. -/
theorem timeoutBlockedThreads_eq_fold (st : SystemState) (scId : SeLe4n.SchedContextId)
    (execCore : CoreId) :
    timeoutBlockedThreads st scId execCore =
      (schedContextTimeoutThreads st scId).foldl (timeoutBlockedThreadStep execCore)
        (st, [], []) := by
  unfold timeoutBlockedThreads schedContextTimeoutThreads
  cases st.getSchedContext? scId with
  | none => rfl
  | some sc => dsimp only; cases sc.boundThread <;> rfl



-- ============================================================================
-- Z4-F: SchedContext-aware budget decrement (timerTickBudget)
-- ============================================================================

/-- Z4-F: SchedContext-aware timer tick budget handling.

Dispatches on the current thread's `schedContextBinding`:
- **Unbound** (Z4-F1): Delegates to the existing time-slice decrement logic.
- **Bound, head not used up** (Z4-F2): charges the unit (`SchedContext.chargeBudget`).
- **Bound, head used up** (Z4-F3, `SchedContext.tickExhausts`): Budget exhausted —
  charges it, inserts the context into the system replenish queue at its place,
  preempts the current thread
  (re-enqueue + reschedule).

Returns `(updatedState, wasPreempted)`. Callers use `wasPreempted` to decide
whether to call `schedule`.

`hTcb` is the witness that `tcb` is the TCB stored at `tid` (`v0.35.67`): the
TCB writes are `SystemState.rewriteObject` under it, so the update is one
in-place table insert whose admissibility proof is erased — and the precondition
the raw insert used to trust silently (a caller passing the stored TCB) is the
signature's.  A caller supplies it from `getTcbWitnessed?`.  The SchedContext
writes are the rewrite under the witnessed lookup of the binding's context. -/
noncomputable def timerTickBudget (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb)
    : Except KernelError (SystemState × Bool) :=
  match tcb.schedContextBinding with
  | .unbound =>
    -- Z4-F1: Legacy path — mirrors `timerTick` exactly.
    -- AC2-C: Now uses configurable `configDefaultTimeSlice` from scheduler state,
    -- matching the updated `timerTick`. See timerTick for proof chain details.
    if tcb.timeSlice ≤ 1 then
      let tcb' := { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }
      let st' := { st.rewriteObject tid.toObjId (.tcb tcb')
                     (SystemState.rewriteAdmissible_tcb hTcb tcb') with
                   machine := tick st.machine }
      -- AI3-A (M-04) / AK2-A (S-H03): Re-enqueue at
      -- `tcb.boostedPriority`. This is the `.unbound` branch so
      -- `TCB.boostedPriority` is unambiguously correct (no SchedContext
      -- resolution needed). SC-bound branches at lines :696 and :716 use
      -- `resolveInsertPriority` directly.
      let st'' := { st' with scheduler := st'.scheduler.setRunQueueOnCore bootCoreId (((st'.scheduler.runQueueOnCore bootCoreId).insert tid (tcb.boostedPriority))) }
      .ok (st'', true)
    else
      let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
      .ok ({ st.rewriteObject tid.toObjId (.tcb tcb')
               (SystemState.rewriteAdmissible_tcb hTcb tcb') with
             machine := tick st.machine }, false)
  | .bound scId | .donated scId _ =>
    match st.getSchedContextWitnessed? scId with
    | some ⟨sc, hSc⟩ =>
      if sc.tickExhausts st.machine.timer then
        -- Z4-F3: Budget exhausted — charge the unit and preempt.

        -- WS-ZA ZA6.4: the charge is seL4-MCS's (`SchedContext.chargeBudget`):
        -- the unit run from `now` (the timer advances after this tick) is
        -- charged against the head refill, the used head is scheduled again one
        -- period after its release (`schedule_used`), and the context waits on
        -- the release queue for its first pending refill (`releaseKey?`).
        let now := st.machine.timer
        let sc''' := cbsUpdateDeadline (sc.chargeBudget now 1 (now + 1)) now true
        -- Write updated SchedContext back (the in-place rewrite under the witnessed lookup)
        let st' := { st.rewriteObject scId.toObjId (.schedContext sc''')
                       (SystemState.rewriteAdmissible_schedContext hSc sc''') with
          machine := tick st.machine }
        -- Insert into system replenish queue at the context's place
        let rq := match sc'''.releaseKey? with
          | some t => (st'.scheduler.replenishQueueOnCore bootCoreId).insert scId t
          | none => st'.scheduler.replenishQueueOnCore bootCoreId
        -- AG1-A: Re-enqueue current thread at effective priority (base + PIP boost)
        let st'' := { st' with scheduler := ((st'.scheduler.setReplenishQueueOnCore bootCoreId rq).setRunQueueOnCore bootCoreId ((st'.scheduler.runQueueOnCore bootCoreId).insert tid (resolveInsertPriority st' tid sc))) }
        -- Z6-E: Timeout any threads blocked on IPC whose timeout was bounded
        -- by this SchedContext. Budget is now 0, so all such threads must unblock.
        -- AK2-D (S-M02): Errors are surfaced via the diagnostic
        -- `SchedulerState.lastTimeoutErrors` field instead of being silently
        -- discarded. A non-empty list indicates an invariant violation. Under
        -- `crossSubsystemInvariant`, the list is always empty.
        -- PR #880 round 8: the timeout wake is target-aware, so on this
        -- boot-core (single-core model) path a woken thread lands on its home
        -- queue.  The SGI component is dropped here: the single-core surface
        -- has no SGI seam (the live kernel runs the per-core
        -- `timerTickBudgetOnCore`, which propagates it), and an SGI can only
        -- arise for an affinity-bound thread the single-core model never runs.
        let (st''', timeoutErrors, _timeoutSgis) := timeoutBlockedThreads st'' scId bootCoreId
        let st'''' := { st''' with scheduler :=
          st'''.scheduler.setLastTimeoutErrorsOnCore bootCoreId timeoutErrors }
        .ok (st'''', true)
      else
        -- Z4-F2: Budget remains — charge the unit and continue
        let now := st.machine.timer
        let sc' := sc.chargeBudget now 1 (now + 1)
        let st' := { st.rewriteObject scId.toObjId (.schedContext sc')
                       (SystemState.rewriteAdmissible_schedContext hSc sc') with
          machine := tick st.machine }
        .ok (st', false)
    | none =>
      -- R5.E (DEEP-SCH-04): SchedContext lookup failed for a bound-budget
      -- thread.  Pre-R5 this silently fell back to a no-preempt
      -- `(state, false)` so the kernel kept running on stale state.  The
      -- runtime-checked `crossSubsystemInvariant`
      -- (`schedContextStoreConsistent`) makes the branch unreachable, but
      -- making the rejection explicit means the diagnostic surfaces if the
      -- invariant ever drifts (e.g., a future cross-subsystem operation
      -- forgets to update the SchedContext table on retype) rather than
      -- being absorbed.  The timer is NOT advanced on the error path: the
      -- `.error` short-circuit returns before any state update, so the
      -- caller (`timerTickWithBudget`) propagates the error to its caller
      -- without committing the partial budget accounting.  This is the
      -- correct fail-closed semantics — a kernel that cannot account for
      -- the current thread's tick must halt the operation cleanly rather
      -- than advance time on an inconsistent budget state.
      .error .missingSchedContext

-- ============================================================================
-- Z4-I: Budget-aware schedule (must precede timerTickWithBudget)
-- ============================================================================

/-- Z4-I / AN5-C: **Budget-aware** SchedContext-aware schedule that uses
effective thread selection. Naming-convention note: `Effective` here is
semantically equivalent to `_budgetAware` — the function filters by
budget eligibility and resolves effective priorities from SchedContext.
Threads with exhausted CBS budgets are automatically skipped during
selection. The primary `schedule` transition is preserved for backward
compatibility (unbound threads + legacy test fixtures). Production boot
paths use `scheduleEffective` via `timerTickWithBudget`. -/
noncomputable def scheduleEffective : Kernel Unit :=
  fun st =>
    match chooseThreadEffective st with
    | .error e => .error e
    | .ok (none, st') =>
        let stSaved := saveOutgoingContext st'
        setCurrentThread none stSaved
    | .ok (some tid, st') =>
        match st'.getTcb? tid with
        | some tcb =>
            if tid ∈ (st'.scheduler.runQueueOnCore bootCoreId) ∧ tcb.domain = (st'.scheduler.activeDomainOnCore bootCoreId) then
              let stSaved := saveOutgoingContext st'
              let stDequeued := { stSaved with scheduler := stSaved.scheduler.setRunQueueOnCore bootCoreId ((stSaved.scheduler.runQueueOnCore bootCoreId).remove tid) }
              let stRestored := restoreIncomingContext stDequeued tid
              setCurrentThread (some tid) stRestored
            else
              .error .schedulerInvariantViolation
        | none => .error .schedulerInvariantViolation

-- ============================================================================
-- Z4-H: Integrated timerTick with replenishment and budget
-- ============================================================================

/-- Z4-H / AN5-C: **Budget-aware** extended timer tick with CBS
replenishment and budget accounting. Naming-convention note: the
`WithBudget` suffix is semantically equivalent to `_budgetAware` used in
the AN5-C documentation — this is the primary timer entry point for
production boot paths.

This replaces the original `timerTick` as the primary timer entry point.
Processing order:
1. Process due replenishments (may re-enqueue budget-restored threads)
2. Handle current thread's budget (unbound: time-slice; bound: CBS budget)
3. If preempted, call `schedule` to select next thread

The original `timerTick` is preserved as `timerTickLegacy` for backward
compatibility with existing preservation proofs. -/
noncomputable def timerTickWithBudget : Kernel Unit :=
  fun st =>
    -- AK2-D (S-M02): clear the diagnostic timeout-error record at the start of
    -- each tick so a stale list never survives across rounds.
    let st := { st with scheduler :=
      st.scheduler.setLastTimeoutErrorsOnCore bootCoreId [] }
    -- Step 1: Process due replenishments
    let now := st.machine.timer
    let stReplenished := processReplenishmentsDue st now
    -- Step 2: Handle current thread's budget
    match (stReplenished.scheduler.currentOnCore bootCoreId) with
    | none =>
      -- No current thread: just advance the timer
      .ok ((), { stReplenished with machine := tick stReplenished.machine })
    | some tid =>
      match stReplenished.getTcbWitnessed? tid with
      | some ⟨tcb, hTcb⟩ =>
        match timerTickBudget stReplenished tid tcb hTcb with
        | .error e => .error e
        | .ok (st', true) =>
          -- Preempted: reschedule using effective selection
          scheduleEffective st'
        | .ok (st', false) =>
          -- Not preempted: continue
          .ok ((), st')
      | none => .error .schedulerInvariantViolation

-- ============================================================================
-- Z4-J: Budget-aware handleYield
-- ============================================================================

/-- Z4-J: Extended yield with SchedContext budget handling.

When a SchedContext-bound thread yields:
1. Charges the head refill in full (seL4-MCS's yield charge, WS-ZA ZA6.4)
2. Inserts the context into the system queue at its place (`releaseKey?`)

3. Re-enqueues at updated deadline/priority
4. Calls `schedule` to select next thread

Unbound threads use the existing yield path (insert + rotateToBack). -/
noncomputable def handleYieldWithBudget : Kernel Unit :=
  fun st =>
    match (st.scheduler.currentOnCore bootCoreId) with
    | none => .error .invalidArgument
    | some tid =>
      match st.getTcb? tid with
      | some tcb =>
        match tcb.schedContextBinding with
        | .unbound =>
          -- AI3-A (M-04): Legacy yield with effective priority (base + PIP boost)
          let rq' := ((st.scheduler.runQueueOnCore bootCoreId).insert tid (tcb.boostedPriority)).rotateToBack tid
          let st' := { st with scheduler := st.scheduler.setRunQueueOnCore bootCoreId rq' }
          scheduleEffective st'
        | .bound scId | .donated scId _ =>
          match st.getSchedContextWitnessed? scId with
          | some ⟨sc, h⟩ =>
            -- WS-ZA ZA6.4: the head refill is charged in full and scheduled one
            -- period after its release (seL4-MCS's yield charge)
            let now := st.machine.timer
            let sc'' := sc.chargeBudget now sc.budget.val now
            -- Insert into replenish queue at the context's place
            let rq := match sc''.releaseKey? with
              | some t => (st.scheduler.replenishQueueOnCore bootCoreId).insert scId t
              | none => st.scheduler.replenishQueueOnCore bootCoreId
            -- Write updated SchedContext (the in-place rewrite under the witnessed lookup)
            let st' := { st.rewriteObject scId.toObjId (.schedContext sc'')
                           (SystemState.rewriteAdmissible_schedContext h sc'') with
              scheduler := st.scheduler.setReplenishQueueOnCore bootCoreId rq }
            -- AG1-A: Re-enqueue thread at effective priority (base + PIP boost)
            let rq' := (st'.scheduler.runQueueOnCore bootCoreId).insert tid (resolveInsertPriority st' tid sc)
            let st'' := { st' with scheduler := st'.scheduler.setRunQueueOnCore bootCoreId rq' }
            scheduleEffective st''
          | none =>
            -- SchedContext not found — fall back to legacy yield
            -- AI3-A (M-04): Use effective priority (base + PIP boost)
            let rq' := ((st.scheduler.runQueueOnCore bootCoreId).insert tid (tcb.boostedPriority)).rotateToBack tid
            let st' := { st with scheduler := st.scheduler.setRunQueueOnCore bootCoreId rq' }
            scheduleEffective st'
      | none => .error .schedulerInvariantViolation

-- ============================================================================
-- M-05/WS-E6: Domain scheduling
-- ============================================================================

/-- M-05/WS-E6: Compatibility alias for domain-aware scheduling selection.

`chooseThread` is now domain-aware; this entry point remains for call sites that
expect explicit domain-oriented naming. -/
noncomputable def chooseThreadInDomain : Kernel (Option SeLe4n.ThreadId) :=
  chooseThread

/-- WS-H12b/H-04: Advance the domain schedule to the next entry.

If the domain schedule is empty (single-domain mode), this is a no-op.
Otherwise, saves the outgoing thread's register context (U-M39), re-enqueues
the current thread (if any) into the run queue, wraps the index modularly
through the schedule table, and updates the active domain and time remaining.

This function is self-contained: it embeds `saveOutgoingContext` internally
so callers do not need to save context before calling. The save occurs before
`current` is set to `none`, ensuring registers are captured while the outgoing
thread identity is still known.

Under dequeue-on-dispatch, the outgoing thread must return to the
runnable pool for its next domain slot.

**Dual-state pattern (S-05)**: This function reads scheduler state from `st`
(the original state) but returns a state based on `stSaved` (after context
save via `saveOutgoingContext`). This split is correct because:
- `saveOutgoingContext` only modifies `objects` (saves the outgoing thread's
  register file into its TCB). It does NOT modify `scheduler`.
- Therefore `st.scheduler = stSaved.scheduler` — all scheduler field reads
  from `st` yield the same values as reads from `stSaved`.
- The result must use `stSaved` (not `st`) as the base because the returned
  state must include the saved register context in the object store.
- Formal guarantee: `saveOutgoingContext_scheduler` (Core.lean:19)
  mechanizes the proof that `(saveOutgoingContext st).scheduler = st.scheduler`. -/
noncomputable def switchDomain : Kernel Unit :=
  fun st =>
    let schedule := st.scheduler.domainSchedule
    match schedule with
    | [] => .ok ((), st)  -- single-domain mode: no-op
    | _ =>
        let nextIdx := ((st.scheduler.domainScheduleIndexOnCore bootCoreId) + 1) % schedule.length
        match schedule[nextIdx]? with
        -- AK2-I (S-M07): Surface `.schedulerInvariantViolation` on the unreachable
        -- fallback. `nextIdx = (idx + 1) % schedule.length` is in bounds for any
        -- non-empty `schedule` (see `switchDomain_index_in_bounds` below), so this
        -- branch is dead under `domainScheduleEntriesPositive`. Previously returned
        -- `.ok ((), st)` — a boot-config bug that violated the invariant would
        -- silently halt domain rotation. Emitting an error makes the invariant
        -- violation observable and testable.
        | none => .error .schedulerInvariantViolation
        | some entry =>
            -- U-M39: Save outgoing context before clearing current
            let stSaved := saveOutgoingContext st
            -- WS-H12b / AI3-A / AK2-A (S-H03): re-enqueue current thread
            -- before the domain switch at `tcb.boostedPriority`
            -- (priority + PIP boost). All reads use `st` (pre-save) so that
            -- TCB fields see the same snapshot; `saveOutgoingContext` only
            -- updates the register-context of the outgoing TCB (not priority,
            -- pipBoost, or schedContextBinding). Under the AK2-B Option B
            -- propagation invariant, this value equals
            -- `(resolveEffectivePrioDeadline st tcb).1` read by selection.
            let rq' := match (st.scheduler.currentOnCore bootCoreId) with
              | none => (st.scheduler.runQueueOnCore bootCoreId)
              | some tid =>
                  match st.getTcb? tid with
                  | some tcb =>
                      (st.scheduler.runQueueOnCore bootCoreId).insert tid (tcb.boostedPriority)
                  | none => (st.scheduler.runQueueOnCore bootCoreId)
            let sched' := ((((st.scheduler.setRunQueueOnCore bootCoreId rq').setCurrentOnCore
                  bootCoreId none).setActiveDomainOnCore bootCoreId (DomainScheduleEntry.domain entry)).setDomainTimeRemainingOnCore
                  bootCoreId (DomainScheduleEntry.length entry)).setDomainScheduleIndexOnCore bootCoreId nextIdx
            .ok ((), { stSaved with scheduler := sched' })

/-- LOW-04: The modular index computation in `switchDomain` always produces a valid
index into a non-empty domain schedule. This formalizes the argument that the
`| none =>` fallback branch is unreachable when the schedule is non-empty. -/
theorem switchDomain_index_in_bounds
    (schedule : List DomainScheduleEntry)
    (idx : Nat) (hNe : schedule ≠ []) :
    ((idx + 1) % schedule.length) < schedule.length := by
  have hPos : 0 < schedule.length := by
    cases schedule with
    | nil => exact absurd rfl hNe
    | cons _ _ => simp
  exact Nat.mod_lt _ hPos

/-- Corollary: the `List.getElem?` lookup in `switchDomain` always returns `some`
for a non-empty schedule, confirming the `| none =>` branch is dead code. -/
theorem switchDomain_index_lookup_isSome
    (schedule : List DomainScheduleEntry)
    (idx : Nat) (hNe : schedule ≠ []) :
    (schedule[(idx + 1) % schedule.length]?).isSome = true := by
  have hBound := switchDomain_index_in_bounds schedule idx hNe
  simp [List.getElem?_eq_getElem hBound]

/-- `switchDomain` preserves `objects.invExt`. In no-op branches the state is
unchanged; in the active branch the objects come from `saveOutgoingContext`,
which preserves the Robin Hood invariant. -/
theorem switchDomain_preserves_objects_invExt
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil => simp [hSched] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hObjInv
  | cons entry rest =>
      simp [hSched] at hStep
      split at hStep
      · -- AK2-I: fallback now emits `.error`, so this arm is discharged by contradiction.
        simp at hStep
      · simp at hStep; obtain ⟨_, rfl⟩ := hStep; dsimp
        exact saveOutgoingContext_preserves_objects_invExt st hObjInv

/-- M-05/WS-E6: Handle a domain tick. Decrements the domain time remaining;
if expired, switches to the next domain and reschedules. -/
noncomputable def scheduleDomain : Kernel Unit :=
  fun st =>
    if (st.scheduler.domainTimeRemainingOnCore bootCoreId) ≤ 1 then
      match switchDomain st with
      | .error e => .error e
      | .ok ((), st') => schedule st'
    else
      let sched' := st.scheduler.setDomainTimeRemainingOnCore bootCoreId
        ((st.scheduler.domainTimeRemainingOnCore bootCoreId) - 1)
      .ok ((), { st with scheduler := sched' })

-- ============================================================================
-- WS-SM SM5.D — Per-core timer tick (production transitions)
-- ============================================================================
--
-- The per-core timer tick (plan §3.4): each core's ARM Generic Timer (CNTP)
-- fires locally; the handler advances *that core's* domain accounting, processes
-- CBS replenishment for its replenish queue (cross-core-waking refilled threads
-- onto their target core via SM5.C's `wakeThread`), and emits a local preemption
-- if the running thread's budget / time-slice is exhausted.  Each transition is
-- the per-core analogue of the single-core production timer machinery
-- (`processReplenishmentsDue`, `timerTickBudget`, `scheduleEffective`,
-- `switchDomain`/`scheduleDomain`), indexed by an explicit `(c : CoreId)` and
-- reading / writing only core `c`'s scheduler slots (plus the shared object
-- store and — for the cross-core replenish wake — the target core's run queue).
--
-- **Global-timer ownership (SMP per-core decision).**  Unlike the single-core
-- `timerTickWithBudget`, the per-core tick does **not** advance the shared
-- `machine.timer` (the abstract global tick counter).  On real hardware each
-- core's CNTP is independent, but the *global* monotonic tick count is
-- maintained by a single authority — exactly mirroring the Rust HAL, where
-- `TICK_COUNT` is "primary-owned" and `init_timer_secondary` deliberately does
-- **not** reset or advance it (SM1.C.4).  A per-core tick that advanced
-- `machine.timer` would over-count it `numCores`× per real tick.  Each per-core
-- tick therefore *reads* `now := machine.timer` (the current global time, the
-- same value every core sees in a round) for CBS replenishment scheduling but
-- never mutates it; the boot core's global tick (or the FFI `ffi_timer_reprogram`)
-- owns the advance.

/-- WS-SM SM5.D.6 (plan §3.4 / §3.7): per-core domain-time decrement + rotation.

Advances core `c`'s domain accounting by one tick: if `domainTimeRemainingOnCore
c` has reached its last tick (`≤ 1`), rotate to the next entry of the
(system-wide) `domainSchedule` — writing core `c`'s `activeDomainOnCore`,
`domainTimeRemainingOnCore` (reset to the new entry's length), and
`domainScheduleIndexOnCore` slots; otherwise decrement core `c`'s
`domainTimeRemainingOnCore`.

This is the **non-boundary** domain-time decrement: it writes **only** core `c`'s
`domainTimeRemainingOnCore` slot and touches neither `current`, any run queue, nor
the active domain.  It is the `else`-branch helper of `scheduleDomainOnCore`
(below), invoked only when `domainTimeRemainingOnCore c > 1`, so the saturating
`- 1` stays `≥ 1` (preserving `domainTimeRemainingPositive`).  Domain *rotation*
(`activeDomainOnCore` advance) is **not** done here — it is coupled atomically
with re-dispatch in `scheduleDomainOnCore`'s boundary branch
(`switchDomainOnCore` + `scheduleEffectiveOnCore`), exactly as the single-core
`scheduleDomain` couples `switchDomain` with `schedule`.  Crucially the per-core
*timer tick* (`timerTickOnCore`) does **not** call this (nor any domain step):
domain accounting is the separate `scheduleDomainOnCore` transition, mirroring the
single-core split where `timerTickWithBudget` never touches `domainTimeRemaining`.
This decoupling is what keeps a running thread from ever outliving its domain (the
audit-pass-2 `currentThreadInActiveDomain` faithfulness fix). -/
def decrementDomainTimeOnCore (st : SystemState) (c : CoreId) : SystemState :=
  let dtr := (st.scheduler.domainTimeRemainingOnCore c) - 1
  { st with scheduler := st.scheduler.setDomainTimeRemainingOnCore c dtr }

/-- WS-SM SM5.D (per-core context save): save core `c`'s current thread's machine
registers into its TCB `registerContext`.  The per-core analogue of
`saveOutgoingContext` (Selection.lean), reading `currentOnCore c` instead of the
boot core's slot and routing the TCB lookup through the typed `getTcb?` accessor
(AK7-clean).  No-op when core `c` is idle or the current TCB fails to resolve
(unreachable under `currentThreadValidOnCore`). -/
def saveOutgoingContextOnCore (st : SystemState) (c : CoreId) : SystemState :=
  match st.scheduler.currentOnCore c with
  | none => st
  | some outTid =>
      -- One TCB rewritten in place through the lookup that is its own witness.
      st.updateTcb outTid fun outTcb => { outTcb with registerContext := st.machine.regsOnCore c }

/-- WS-ZA ZA4.5: **the compiled save.**  The core's words are written into
the file the outgoing TCB already owns (`RegisterFile.overwriteWith`), read off
the machine before the object store is written, so the write's closure holds
the core's file rather than the whole state (which would leave the object
table shared, and the table and the TCB copied), and the TCB and the core never
share a file for the next restore to copy.  Proven equal
(`saveOutgoingContextOnCore_eq_impl`). -/
def saveOutgoingContextOnCoreImpl (st : SystemState) (c : CoreId) : SystemState :=
  match st.scheduler.currentOnCore c with
  | none => st
  | some outTid =>
      let regs := st.machine.regsOnCore c
      st.updateTcb outTid fun outTcb =>
        { outTcb with registerContext := RegisterFile.overwriteWith regs outTcb.registerContext }

@[csimp] theorem saveOutgoingContextOnCore_eq_impl :
    @saveOutgoingContextOnCore = @saveOutgoingContextOnCoreImpl := by
  funext st c
  unfold saveOutgoingContextOnCore saveOutgoingContextOnCoreImpl
  split
  · rfl
  · simp only [RegisterFile.overwriteWith_eq]

/-- WS-SM SM5.D (frame): the per-core context save writes only the object
store — the scheduler state passes through untouched on every arm. -/
@[simp] theorem saveOutgoingContextOnCore_scheduler (st : SystemState) (c : CoreId) :
    (saveOutgoingContextOnCore st c).scheduler = st.scheduler := by
  unfold saveOutgoingContextOnCore
  split
  · rfl
  · exact SystemState.updateTcb_scheduler _ _ _

/-- WS-SM SM5.E (idle-dispatch admission): is core `c`'s idle thread a *safe*
dispatch target — installed, in core `c`'s active domain, **and admissible on core
`c`** (its `cpuAffinity` admits `c`)?  This gates the idle fallback in
`scheduleEffectiveOnCore`'s `none` branch: it ensures the post-dispatch state
satisfies `currentThreadValidOnCore` (idle resolves) and
`currentThreadInActiveDomainOnCore` (idle's domain matches).  The
`affinityAdmitsCore` conjunct mirrors `switchToThreadOnCore`'s reject-remote guard:
it guarantees the core-local idle property even if the reserved idle slot were ever
populated with a TCB bound to a *different* core (`cpuAffinity = some c'`, `c' ≠ c`)
— such a TCB is **not** dispatchable as core `c`'s idle thread.  Fail-closed: an
absent / out-of-domain / remote-bound idle thread is not dispatchable, and the
core falls back to the legacy `current = none` idle representation. -/
def idleDispatchableOnCore (st : SystemState) (c : CoreId) : Bool :=
  match st.getTcb? (idleThreadId c) with
  | some tcb => tcb.domain == st.scheduler.activeDomainOnCore c && affinityAdmitsCore tcb c
  | none => false

/-- WS-SM SM5.E: the idle-dispatch state — core `c`'s idle thread becomes current
via the same dequeue-on-dispatch (`RunQueue.remove`) + context-restore
(`restoreIncomingContext`) + set-current sequence a normal switch uses.  Factored
out of `scheduleEffectiveOnCore`'s idle branch so its frame lemmas prove once that
it touches only core `c`'s scheduler slots, `machine.regs` and the run-queue links
the dequeue rewrites (WS-ZA ZA4.5) — no other object field. -/
def dispatchIdleOnCore (st : SystemState) (c : CoreId) : SystemState :=
  let stDeq := st.runRemoveOnCore c (idleThreadId c)
  let stRestored := restoreIncomingContextOnCore stDeq c (idleThreadId c)
  { stRestored with scheduler := stRestored.scheduler.setCurrentOnCore c (some (idleThreadId c)) }

/-- WS-SM SM5.E: dispatching idle sets core `c`'s current thread to the idle thread. -/
@[simp] theorem dispatchIdleOnCore_currentOnCore (st : SystemState) (c : CoreId) :
    (dispatchIdleOnCore st c).scheduler.currentOnCore c = some (idleThreadId c) := by
  simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_currentOnCore_self]

/-- WS-SM SM5.E: dispatching idle touches the object store only in the run-queue
links its dequeue rewrites (WS-ZA ZA4.5). -/
theorem dispatchIdleOnCore_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId) :
    (dispatchIdleOnCore st c).objectsAgreeOffRunLinks st :=
  .trans (.of_objects_eq (restoreIncomingContextOnCore_objects _ _ _))
    (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c (idleThreadId c))

/-- WS-SM SM5.E: after dispatching idle, core `c`'s run queue is the old one with
the idle thread removed (dequeue-on-dispatch). -/
theorem dispatchIdleOnCore_runQueueOnCore (st : SystemState) (c : CoreId) :
    (dispatchIdleOnCore st c).scheduler.runQueueOnCore c
      = (st.scheduler.runQueueOnCore c).remove (idleThreadId c) := by
  simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_runQueueOnCore,
    restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
    SchedulerState.setRunQueueOnCore_runQueueOnCore_self]

/-- WS-SM SM5.E: dispatching idle frames every core's active domain. -/
@[simp] theorem dispatchIdleOnCore_activeDomainOnCore (st : SystemState) (c c' : CoreId) :
    (dispatchIdleOnCore st c).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' := by
  simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_activeDomainOnCore,
    restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
    SchedulerState.setRunQueueOnCore_activeDomainOnCore,
    SchedulerState.setRunQueueEndsOnCore_activeDomainOnCore]

/-- WS-SM SM5.E: dispatching idle leaves every thread's TCB resolution unchanged
past its run-queue links. -/
theorem dispatchIdleOnCore_getTcb? (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    ((dispatchIdleOnCore st c).getTcb? tid).map TCB.withoutRunLinks
      = (st.getTcb? tid).map TCB.withoutRunLinks :=
  (dispatchIdleOnCore_objectsAgreeOffRunLinks st c).getTcb? tid

/-- WS-SM SM5.I (per-core register banks): dispatching idle restores the idle
thread's register context into **core `c`'s** bank.  The dequeue rewrites only
run-queue links (so the idle TCB's `registerContext` is unchanged), the per-core
restore writes `setRegsOnCore c idleTcb.registerContext`, and the trailing
`setCurrentOnCore` frames `machine`. -/
theorem dispatchIdleOnCore_machine_regsOnCore_self (st : SystemState) (c : CoreId)
    (idleTcb : TCB) (hTcb : st.getTcb? (idleThreadId c) = some idleTcb) :
    (dispatchIdleOnCore st c).machine.regsOnCore c = idleTcb.registerContext := by
  unfold dispatchIdleOnCore
  obtain ⟨t', h', hE⟩ :=
    (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c (idleThreadId c)).getTcb?_some hTcb
  rw [← TCB.proj_eq_of_withoutRunLinks_eq TCB.registerContext hE]
  exact restoreIncomingContextOnCore_regsOnCore_self _ c (idleThreadId c) t' h'

/-- WS-SM SM5.E: the per-core idle fallback applied to an already-context-saved
state — run core `c`'s idle thread if dispatchable, else leave `current = none`.
Factored as a named helper (rather than an inline `if`) so `scheduleEffectiveOnCore`'s
`none` branch is a clean `.ok (idleFallbackOnCore stSaved c)`, and the idle/none
case analysis is discharged *once* in this helper's lemmas instead of inside every
`scheduleEffectiveOnCore` establishment proof. -/
def idleFallbackOnCore (st : SystemState) (c : CoreId) : SystemState :=
  if idleDispatchableOnCore st c then dispatchIdleOnCore st c
  else { st with scheduler := st.scheduler.setCurrentOnCore c none }

/-- WS-SM SM5.E: the idle fallback touches the object store only in the run-queue
links the idle dispatch's dequeue rewrites (WS-ZA ZA4.5); the `current = none`
arm leaves `objects` unchanged. -/
theorem idleFallbackOnCore_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId) :
    (idleFallbackOnCore st c).objectsAgreeOffRunLinks st := by
  unfold idleFallbackOnCore
  split
  · exact dispatchIdleOnCore_objectsAgreeOffRunLinks st c
  · exact .refl _

/-- WS-SM SM5.E: the idle fallback frames every thread's TCB resolution, past its
run-queue links. -/
theorem idleFallbackOnCore_getTcb? (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    ((idleFallbackOnCore st c).getTcb? tid).map TCB.withoutRunLinks
      = (st.getTcb? tid).map TCB.withoutRunLinks :=
  (idleFallbackOnCore_objectsAgreeOffRunLinks st c).getTcb? tid

/-- WS-SM SM5.E: the idle fallback preserves the object-store invariant — the idle
arm's dequeue writes only run-queue links in place (WS-ZA ZA4.5). -/
theorem idleFallbackOnCore_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (idleFallbackOnCore st c).objects.invExt := by
  unfold idleFallbackOnCore
  split
  · simp only [dispatchIdleOnCore, restoreIncomingContextOnCore_objects]
    exact SystemState.runRemoveOnCore_objects_invExt st c _ hInv
  · exact hInv

/-- WS-SM SM5.E: the idle fallback's run queue is the old one with the idle thread
removed (idle dispatch) or unchanged (`current = none`) — in both arms a *subset*
of the old run queue (idle dispatch only `remove`s). -/
theorem idleFallbackOnCore_runQueueOnCore_mem (st : SystemState) (c : CoreId)
    (x : SeLe4n.ThreadId) (hx : x ∈ (idleFallbackOnCore st c).scheduler.runQueueOnCore c) :
    x ∈ st.scheduler.runQueueOnCore c := by
  unfold idleFallbackOnCore at hx
  split at hx
  · rw [dispatchIdleOnCore_runQueueOnCore] at hx
    exact ((RunQueue.mem_remove _ _ _).mp hx).1
  · simpa [SchedulerState.setCurrentOnCore_runQueueOnCore] using hx

/-- WS-SM SM5.D.5 (per-core budget-aware reschedule): the per-core analogue of
`scheduleEffective` (Core.lean).  Re-selects core `c`'s highest-priority
*budget-eligible* runnable thread (`chooseThreadEffectiveOnCore`, SM5.A §6) and
dispatches it with the inline save→dequeue→restore→set-current sequence, reading
/ writing **only** core `c`'s scheduler slots (`currentOnCore c`,
`runQueueOnCore c`, `activeDomainOnCore c`) plus the shared object store and
`machine.regs` (the executing core's register file).

This is the *drop-current* dispatch (it does **not** re-enqueue the previous
current — the caller `timerTickOnCore` has already re-enqueued it via
`timerTickBudgetOnCore`, exactly as the single-core `timerTickWithBudget` →
`scheduleEffective` pairing).  The selected thread is dequeued-on-dispatch
(SM5.B.5); if it is core `c`'s previously-current thread re-selected, it simply
continues running with a fresh time-slice / budget.

A selected `tid` that resolves to no TCB or lies outside core `c`'s active
domain surfaces `.schedulerInvariantViolation` (a corrupted selection, never
silently dispatched); the selection walks only core `c`'s queue, so — as in
seL4's `chooseThread` — the dispatch does not re-check membership (WS-ZA ZA4.5:
it would read the ghost queue). -/
def scheduleEffectiveOnCore (st : SystemState) (c : CoreId) :
    Except KernelError SystemState :=
  match chooseThreadEffectiveOnCore st c with
  | .error e => .error e
  | .ok none =>
      -- WS-SM SM5.E (folded idle dispatch): nothing budget-eligible is runnable.
      -- Save the outgoing context, then run core `c`'s **idle thread** if it is
      -- dispatchable (installed + in-domain + admissible on `c`); otherwise fall
      -- back to the legacy `current = none` idle representation.  States without an
      -- installed idle thread are unchanged (`idleDispatchableOnCore = false`), so
      -- the single-core boot trace and idle-free fixtures are byte-identical.  This
      -- is what makes the live per-core tick / domain paths (`timerTickOnCore` /
      -- `scheduleDomainOnCore`, which call this) actually run the idle thread.
      -- The reschedule-SGI accumulator (KSC-1): a scheduling point on `c`
      -- clears `c`'s flag as its last write (both `.ok` arms).
      .ok ((idleFallbackOnCore (saveOutgoingContextOnCore st c) c).clearReschedulePendingOnCore c)
  | .ok (some tid) =>
      match st.getTcb? tid with
      | some tcb =>
          if tcb.domain = (st.scheduler.activeDomainOnCore c) then
            let stSaved := saveOutgoingContextOnCore st c
            let stDequeued := stSaved.runRemoveOnCore c tid
            let stRestored := restoreIncomingContextOnCore stDequeued c tid
            .ok { stRestored with scheduler := (stRestored.scheduler.setCurrentOnCore c (some tid))
              |>.clearReschedulePendingOnCore c }
          else
            .error .schedulerInvariantViolation
      | _ => .error .schedulerInvariantViolation

/-- WS-ZA ZA4.5: the compiled `scheduleEffectiveOnCore`.  The selection is a
thread code (`chooseThreadEffectiveOnCoreCode`), so no candidate record,
`Option` or `Except` is built for it, and the dispatched thread leaves core
`c`'s run queue through its TCB run-queue links (`runRemoveOnCore`), written in
place.  Proven equal (`scheduleEffectiveOnCore_eq_impl`). -/
def scheduleEffectiveOnCoreImpl (st : SystemState) (c : CoreId) :
    Except KernelError SystemState :=
  match chooseThreadEffectiveOnCoreCode st c with
  | 0 =>
      .ok ((idleFallbackOnCore (saveOutgoingContextOnCore st c) c).clearReschedulePendingOnCore c)
  | k + 1 =>
      let tid : SeLe4n.ThreadId := ⟨k⟩
      match st.getTcb? tid with
      | some tcb =>
          if tcb.domain = (st.scheduler.activeDomainOnCore c) then
            let stSaved := saveOutgoingContextOnCore st c
            let stDequeued := stSaved.runRemoveOnCore c tid
            let stRestored := restoreIncomingContextOnCore stDequeued c tid
            .ok { stRestored with scheduler := (stRestored.scheduler.setCurrentOnCore c (some tid))
              |>.clearReschedulePendingOnCore c }
          else
            .error .schedulerInvariantViolation
      | _ => .error .schedulerInvariantViolation

@[csimp] theorem scheduleEffectiveOnCore_eq_impl :
    @scheduleEffectiveOnCore = @scheduleEffectiveOnCoreImpl := by
  funext st c
  unfold scheduleEffectiveOnCore scheduleEffectiveOnCoreImpl
  rw [chooseThreadEffectiveOnCore_eq_code]
  cases chooseThreadEffectiveOnCoreCode st c <;> rfl

-- ============================================================================
-- §1  The dispatch never refuses
-- ============================================================================

/-- The selection scan names only a thread the store holds and the eligibility
test admits: a found candidate is one, and every improvement is one. -/
theorem chooseBestRunnableEffectiveCode_succ (st : SystemState) (eligible : TCB → Bool) :
    ∀ (l : List SeLe4n.ThreadId) (found : Bool) (bt : SeLe4n.ThreadId) (bp : SeLe4n.Priority)
      (bd : SeLe4n.Deadline) (k : Nat),
      (found = true → ∃ tcb, st.getTcb? bt = some tcb ∧ eligible tcb = true) →
      chooseBestRunnableEffectiveCode st eligible l found bt bp bd = k + 1 →
      ∃ tcb, st.getTcb? ⟨k⟩ = some tcb ∧ eligible tcb = true := by
  intro l
  induction l with
  | nil =>
    intro found bt bp bd k hF h
    unfold chooseBestRunnableEffectiveCode at h
    cases found
    · simp at h
    · simp only [if_true, Nat.add_right_cancel_iff] at h
      obtain ⟨tcb, hT, hE⟩ := hF rfl
      subst h
      exact ⟨tcb, hT, hE⟩
  | cons tid rest ih =>
    intro found bt bp bd k hF h
    unfold chooseBestRunnableEffectiveCode at h
    cases hT : st.getTcb? tid with
    | none => rw [hT] at h; exact ih found bt bp bd k hF h
    | some tcb =>
      rw [hT] at h
      simp only at h
      by_cases hE : (eligible tcb && hasSufficientBudget st tcb) = true
      · rw [if_pos hE] at h
        have hEl : eligible tcb = true := (Bool.and_eq_true _ _ ▸ hE).1
        split at h
        · exact ih true tid _ _ k (fun _ => ⟨tcb, hT, hEl⟩) h
        · exact ih found bt bp bd k hF h
      · rw [if_neg hE] at h
        exact ih found bt bp bd k hF h

/-- Core `c`'s selection names a thread the store holds, in `c`'s active domain. -/
theorem chooseThreadEffectiveOnCoreCode_succ {st : SystemState} {c : CoreId} {k : Nat}
    (h : chooseThreadEffectiveOnCoreCode st c = k + 1) :
    ∃ tcb, st.getTcb? ⟨k⟩ = some tcb ∧ tcb.domain = st.scheduler.activeDomainOnCore c := by
  unfold chooseThreadEffectiveOnCoreCode at h
  have hNone : (false = true → ∃ tcb, st.getTcb? default = some tcb ∧
      (fun tcb : TCB => tcb.domain == st.scheduler.activeDomainOnCore c) tcb = true) :=
    fun h => absurd h Bool.false_ne_true
  dsimp only at h
  split at h
  · obtain ⟨tcb, hT, hE⟩ := chooseBestRunnableEffectiveCode_succ st _ _ false _ _ _ k hNone h
    exact ⟨tcb, hT, beq_iff_eq.mp hE⟩
  · obtain ⟨tcb, hT, hE⟩ := chooseBestRunnableEffectiveCode_succ st _ _ false _ _ _ k hNone h
    exact ⟨tcb, hT, beq_iff_eq.mp hE⟩

/-- `scheduleEffectiveOnCore`'s state, which it always reaches
(`scheduleEffectiveOnCore_eq_state`): the selection names a thread the store
holds in the core's active domain (`chooseThreadEffectiveOnCoreCode_succ`), so
the dispatch's lookup and domain test always pass and the dispatch writes
without a refusal to keep the state for, as seL4's `schedule` never fails. -/
@[inline] def scheduleEffectiveOnCoreState (st : SystemState) (c : CoreId) : SystemState :=
  match chooseThreadEffectiveOnCoreCode st c with
  | 0 => (idleFallbackOnCore (saveOutgoingContextOnCore st c) c).clearReschedulePendingOnCore c
  | k + 1 =>
      let tid : SeLe4n.ThreadId := ⟨k⟩
      let stSaved := saveOutgoingContextOnCore st c
      let stDequeued := stSaved.runRemoveOnCore c tid
      let stRestored := restoreIncomingContextOnCore stDequeued c tid
      { stRestored with scheduler := (stRestored.scheduler.setCurrentOnCore c (some tid))
        |>.clearReschedulePendingOnCore c }

theorem scheduleEffectiveOnCore_eq_state (st : SystemState) (c : CoreId) :
    scheduleEffectiveOnCore st c = .ok (scheduleEffectiveOnCoreState st c) := by
  rw [scheduleEffectiveOnCore_eq_impl]
  unfold scheduleEffectiveOnCoreImpl scheduleEffectiveOnCoreState
  cases hk : chooseThreadEffectiveOnCoreCode st c with
  | zero => rfl
  | succ k =>
    obtain ⟨tcb, hT, hD⟩ := chooseThreadEffectiveOnCoreCode_succ hk
    simp only [hT, hD, ↓reduceIte]


/-- WS-SM SM5.E (deprecated alias).  The idle dispatch is now folded directly into
`scheduleEffectiveOnCore` (its `none` branch runs core `c`'s idle thread when
dispatchable — see above), so the per-core *timer* / *domain* paths
(`timerTickOnCore` / `scheduleDomainOnCore`, which call `scheduleEffectiveOnCore`)
reach the idle thread on the live kernel.  `scheduleOrIdleOnCore` is therefore
definitionally `scheduleEffectiveOnCore`; it is retained as a name for the SM5.E
test / demo / inventory surface (and for callers that want the intent explicit). -/
def scheduleOrIdleOnCore (st : SystemState) (c : CoreId) :
    Except KernelError SystemState :=
  scheduleEffectiveOnCore st c

/-- WS-SM SM5.D.4 (replenishment wake decision): which bound thread, if any, a
CBS replenishment of `scId` should make runnable.

Returns `some tid` exactly when the SchedContext was **exhausted before the
refill** (`stPre`'s `budgetRemaining = 0`) **and is positive after** (`refilled`'s
`budgetRemaining > 0`) **and is bound** to `tid` **and `tid` is runnable**
(`TCB.isRunnable`) — i.e. the thread genuinely transitioned from budget-starved
to runnable.  A no-op refill (already-positive budget) or an unbound SC yields
`none` (no wake), and so does a bound thread blocked in IPC or suspended: its
context gets its budget back, but the thread stays where it is, as in seL4, whose
release queue holds only runnable threads.  The wake writes the thread's IPC
state to `.ready`, so waking a blocked thread would detach it from the endpoint
queue that still links it, and waking a suspended one would run it.  Factored out of
`processOneReplenishmentOnCore` so the latter's state result is cleanly either the
refilled state or a `wakeThread` on top of it.  AK7-clean (typed
`getSchedContext?`). -/
def replenishWakeTarget (stPre refilled : SystemState)
    (scId : SeLe4n.SchedContextId) : Option SeLe4n.ThreadId :=
  let wasExhausted := match stPre.getSchedContext? scId with
    | some sc => sc.budgetRemaining.isZero
    | none    => false
  match refilled.getSchedContext? scId with
  | some sc =>
    if wasExhausted && sc.budgetRemaining.isPositive then
      sc.boundThread.filter fun t => (refilled.getTcb? t).any TCB.isRunnable
    else none
  | none    => none

/-- WS-SM SM5.D.4 (cross-core CBS replenish wakes remote): process **one** due
SchedContext replenishment on the executing core `execCore`.

Refills `scId`'s budget (`refillSchedContext`), and — if its budget went from
exhausted (`0`) to positive — makes its bound thread runnable on its **target**
core via SM5.C's `wakeThread`.  The target core is `determineTargetCore` (the
thread's `cpuAffinity`, or the boot core when unbound); under the
`schedContextRunQueueConsistent_perCore` invariant the target is `execCore`, but
a thread whose affinity changed (SM5.H.4 migration deferred) targets a *remote*
core — the defensive cross-core path SM5.D.4 realises.

Guards (faithful to the single-core `processReplenishmentsDue`): the wake fires
only when the SC was genuinely exhausted-and-now-positive (a no-op refill does
not wake), and never re-enqueues a thread that is *currently running* on some
core (re-enqueuing the running thread would violate dequeue-on-dispatch).
`wakeThread`'s own single-placement guard (`runnableOnSomeCore`) additionally
suppresses a second placement of an already-runnable thread.

**The stale decision is flagged (WS-ZA ZA6.2).**  A wake that resolves to a
thread marks the reschedule flag of the thread's target core
(`markReschedulePendingOnCoreIf`, on a thread the store holds), whether the wake placed the thread or found it
already queued: the refill made a queued thread eligible, which stales that
core's scheduling decision, as seL4's `awaken` calls `possibleSwitchTo` for
every released thread.  The flag is the step's whole report: a remote core's
flag going up is the `.reschedule` SGI the step's seam fires
(`rescheduleSgisFromFlags`), and the executing core's own flag is the local
decision `timerTickOnCore` runs after the charge.  Before ZA6.2 the step
returned the SGI and a local-wake bit beside the state; reading them off the
state lets the drain return the state alone.  The already-queued case is the
one PR #880 round 7 found: a thread queued but exhausted on the executing core,
refilled with no placement and no SGI, waited out the current thread's entire
remaining budget.

This is the refill and the wake; `processOneReplenishmentOnCore` is this step
under the refill's key hook (`markRefillKeyChange`). -/
def refillWakeOnCore (st : SystemState) (execCore : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) : SystemState :=
  let refilled := refillSchedContext st scId now
  match replenishWakeTarget st refilled scId with
  | some tid =>
      if runningOnSomeCore refilled tid then refilled
      else
        let woken := (wakeThread refilled tid execCore).1
        { woken with scheduler := (woken.scheduler.markReschedulePendingOnCoreIf
            (determineTargetCore refilled tid) (refilled.getTcb? tid).isSome) }
  | none => refilled

/-- WS-ZA ZA6.2: the refill's key hook.  A refill reads and writes one
scheduling context, and the only thread whose effective key or budget
eligibility reads that context is the one it names as bound
(`schedContextBindingBidirectional`), so the refill can stale a decision only
through that thread: its deadline moves whenever the refilled budget is positive
(`cbsUpdateDeadline … true`), and it becomes eligible when the budget comes back
from zero.  The hook is the one every writer of a key input runs
(`markKeyChangeFrom`, read against the pre-refill state): it flags each core
whose queue holds the thread when its key moved or it gained candidacy, and the
core it runs on when its key weakened, as seL4's refill path re-sorts the
released thread and calls `possibleSwitchTo`.  A context with no bound thread,
or none at all, stales nothing. -/
def markRefillKeyChange (pre post : SystemState) (scId : SeLe4n.SchedContextId) :
    SystemState :=
  match pre.getSchedContext? scId with
  | some sc =>
    match sc.boundThread with
    | some t => markKeyChangeFrom pre post t
    | none => post
  | none => post

/-- Any projection the flag write leaves alone, the refill's key hook leaves
alone. -/
theorem markRefillKeyChange_extract_frame {F : Type} (extract : SystemState → F)
    (pre post : SystemState) (scId : SeLe4n.SchedContextId)
    (h : ∀ (s : SystemState) c, extract (s.markReschedulePendingOnCore c) = extract s) :
    extract (markRefillKeyChange pre post scId) = extract post := by
  unfold markRefillKeyChange
  split
  · split
    · exact markKeyChangeFrom_extract_frame extract pre post _ h
    · rfl
  · rfl

@[simp] theorem markRefillKeyChange_objects (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).objects = st.objects :=
  markRefillKeyChange_extract_frame (fun s => s.objects) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_queuedOn (pre st : SystemState) (scId : SeLe4n.SchedContextId)
    (c : CoreId) (t : SeLe4n.ThreadId) :
    (markRefillKeyChange pre st scId).queuedOn c t = st.queuedOn c t :=
  (SystemState.RunCoresAgree.of_objects (markRefillKeyChange_objects pre st scId)).queuedOn c t

@[simp] theorem markRefillKeyChange_objectIndex (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).objectIndex = st.objectIndex :=
  markRefillKeyChange_extract_frame (fun s => s.objectIndex) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_machine (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).machine = st.machine :=
  markRefillKeyChange_extract_frame (fun s => s.machine) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_cdt (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).cdt = st.cdt :=
  markRefillKeyChange_extract_frame (fun s => s.cdt) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_irqHandlers (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).irqHandlers = st.irqHandlers :=
  markRefillKeyChange_extract_frame (fun s => s.irqHandlers) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_tlbShootdown (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).tlbShootdown = st.tlbShootdown :=
  markRefillKeyChange_extract_frame (fun s => s.tlbShootdown) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_perCoreTlb (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).perCoreTlb = st.perCoreTlb :=
  markRefillKeyChange_extract_frame (fun s => s.perCoreTlb) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_perCoreICache (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).perCoreICache = st.perCoreICache :=
  markRefillKeyChange_extract_frame (fun s => s.perCoreICache) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_pendingIcacheMaintenance (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).pendingIcacheMaintenance = st.pendingIcacheMaintenance :=
  markRefillKeyChange_extract_frame (fun s => s.pendingIcacheMaintenance) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_pendingPhysicalWrites (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).pendingPhysicalWrites = st.pendingPhysicalWrites :=
  markRefillKeyChange_extract_frame (fun s => s.pendingPhysicalWrites) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_objectIndexSet (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).objectIndexSet = st.objectIndexSet :=
  markRefillKeyChange_extract_frame (fun s => s.objectIndexSet) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_lifecycle (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).lifecycle = st.lifecycle :=
  markRefillKeyChange_extract_frame (fun s => s.lifecycle) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_asidTable (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).asidTable = st.asidTable :=
  markRefillKeyChange_extract_frame (fun s => s.asidTable) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_interfaceRegistry (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).interfaceRegistry = st.interfaceRegistry :=
  markRefillKeyChange_extract_frame (fun s => s.interfaceRegistry) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_tlb (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).tlb = st.tlb :=
  markRefillKeyChange_extract_frame (fun s => s.tlb) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_declassificationAuditLog (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).declassificationAuditLog = st.declassificationAuditLog :=
  markRefillKeyChange_extract_frame (fun s => s.declassificationAuditLog) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_declassificationAuditEpoch (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).declassificationAuditEpoch = st.declassificationAuditEpoch :=
  markRefillKeyChange_extract_frame (fun s => s.declassificationAuditEpoch) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_declassificationRefusals (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).declassificationRefusals = st.declassificationRefusals :=
  markRefillKeyChange_extract_frame (fun s => s.declassificationRefusals) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_declassificationTaint (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).declassificationTaint = st.declassificationTaint :=
  markRefillKeyChange_extract_frame (fun s => s.declassificationTaint) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_getTcb? (pre st : SystemState) (scId : SeLe4n.SchedContextId) (tid' : SeLe4n.ThreadId) :
    (markRefillKeyChange pre st scId).getTcb? tid' = st.getTcb? tid' := by
  unfold SystemState.getTcb?; rw [markRefillKeyChange_objects]

@[simp] theorem markRefillKeyChange_getSchedContext? (pre st : SystemState) (scId : SeLe4n.SchedContextId)
    (sid : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).getSchedContext? sid = st.getSchedContext? sid := by
  unfold SystemState.getSchedContext?; rw [markRefillKeyChange_objects]

@[simp] theorem markRefillKeyChange_runQueueOnCore (pre st : SystemState) (scId : SeLe4n.SchedContextId) (c : CoreId) :
    (markRefillKeyChange pre st scId).scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c :=
  markRefillKeyChange_extract_frame (fun s => s.scheduler.runQueueOnCore c) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_currentOnCore (pre st : SystemState) (scId : SeLe4n.SchedContextId) (c : CoreId) :
    (markRefillKeyChange pre st scId).scheduler.currentOnCore c = st.scheduler.currentOnCore c :=
  markRefillKeyChange_extract_frame (fun s => s.scheduler.currentOnCore c) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_replenishQueueOnCore (pre st : SystemState) (scId : SeLe4n.SchedContextId) (c : CoreId) :
    (markRefillKeyChange pre st scId).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c :=
  markRefillKeyChange_extract_frame (fun s => s.scheduler.replenishQueueOnCore c) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_activeDomainOnCore (pre st : SystemState) (scId : SeLe4n.SchedContextId) (c : CoreId) :
    (markRefillKeyChange pre st scId).scheduler.activeDomainOnCore c
      = st.scheduler.activeDomainOnCore c :=
  markRefillKeyChange_extract_frame (fun s => s.scheduler.activeDomainOnCore c) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_domainTimeRemainingOnCore (pre st : SystemState) (scId : SeLe4n.SchedContextId) (c : CoreId) :
    (markRefillKeyChange pre st scId).scheduler.domainTimeRemainingOnCore c
      = st.scheduler.domainTimeRemainingOnCore c :=
  markRefillKeyChange_extract_frame (fun s => s.scheduler.domainTimeRemainingOnCore c) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_domainScheduleIndexOnCore (pre st : SystemState) (scId : SeLe4n.SchedContextId) (c : CoreId) :
    (markRefillKeyChange pre st scId).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c :=
  markRefillKeyChange_extract_frame (fun s => s.scheduler.domainScheduleIndexOnCore c) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_lastTimeoutErrorsOnCore (pre st : SystemState) (scId : SeLe4n.SchedContextId) (c : CoreId) :
    (markRefillKeyChange pre st scId).scheduler.lastTimeoutErrorsOnCore c
      = st.scheduler.lastTimeoutErrorsOnCore c :=
  markRefillKeyChange_extract_frame (fun s => s.scheduler.lastTimeoutErrorsOnCore c) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_domainSchedule (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).scheduler.domainSchedule = st.scheduler.domainSchedule :=
  markRefillKeyChange_extract_frame (fun s => s.scheduler.domainSchedule) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_configDefaultTimeSlice (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    (markRefillKeyChange pre st scId).scheduler.configDefaultTimeSlice = st.scheduler.configDefaultTimeSlice :=
  markRefillKeyChange_extract_frame (fun s => s.scheduler.configDefaultTimeSlice) pre st scId
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markRefillKeyChange_runnableOnSomeCore (pre st : SystemState)
    (scId : SeLe4n.SchedContextId) (tid' : SeLe4n.ThreadId) :
    runnableOnSomeCore (markRefillKeyChange pre st scId) tid' = runnableOnSomeCore st tid' := by
  unfold runnableOnSomeCore
  simp only [markRefillKeyChange_queuedOn]

@[simp] theorem markRefillKeyChange_placedCoreOf? (pre st : SystemState)
    (scId : SeLe4n.SchedContextId) (tid' : SeLe4n.ThreadId) :
    placedCoreOf? (markRefillKeyChange pre st scId) tid' = placedCoreOf? st tid' := by
  unfold placedCoreOf?
  simp only [markRefillKeyChange_queuedOn, markRefillKeyChange_currentOnCore]

@[simp] theorem markRefillKeyChange_getObject? (pre st : SystemState) (scId : SeLe4n.SchedContextId)
    (oid : SeLe4n.ObjId) :
    (markRefillKeyChange pre st scId).getObject? oid = st.getObject? oid := by
  unfold SystemState.getObject?; rw [markRefillKeyChange_objects]

@[simp] theorem markRefillKeyChange_getReply? (pre st : SystemState) (scId : SeLe4n.SchedContextId)
    (rid : SeLe4n.ReplyId) :
    (markRefillKeyChange pre st scId).getReply? rid = st.getReply? rid := by
  unfold SystemState.getReply?; rw [markRefillKeyChange_objects]


theorem markRefillKeyChange_reschedulePendingOnCore_mono (pre st : SystemState)
    (scId : SeLe4n.SchedContextId) (c : CoreId) (h : st.scheduler.reschedulePendingOnCore c = true) :
    (markRefillKeyChange pre st scId).scheduler.reschedulePendingOnCore c = true := by
  unfold markRefillKeyChange
  split
  · split
    · unfold markKeyChangeFrom
      split
      · exact markKeyChangeFor_reschedulePendingOnCore_mono _ _ _ _
          (markCandidacyGainFor_reschedulePendingOnCore_mono _ _ _ _ h)
      · simp [markReschedulePendingWhere_reschedulePendingOnCore, h]
    · exact h
  · exact h

theorem markRefillKeyChange_eq_with_scheduler (pre st : SystemState) (scId : SeLe4n.SchedContextId) :
    markRefillKeyChange pre st scId =
      { st with scheduler := (markRefillKeyChange pre st scId).scheduler } :=
  markRefillKeyChange_extract_frame
    (fun s => ({ s with scheduler := (markRefillKeyChange pre st scId).scheduler } : SystemState))
    pre st scId (fun _ _ => rfl)

theorem markRefillKeyChange_runQueueStage (pre post : SystemState) (scId : SeLe4n.SchedContextId) :
    SystemState.RunQueueStage post (markRefillKeyChange pre post scId) := by
  unfold markRefillKeyChange
  split
  · split
    · exact markKeyChangeFrom_runQueueStage _ _ _
    · exact SystemState.RunQueueStage.refl _
  · exact SystemState.RunQueueStage.refl _

/-- WS-SM SM5.D.4: process **one** due replenishment on the executing core: the
refill and its wake (`refillWakeOnCore`), under the refill's key hook
(`markRefillKeyChange`, WS-ZA ZA6.2).  The hook closes the stale decisions the
wake does not: a refill of a context that was not exhausted moves its bound
thread's deadline with no wake, and a refill of a running thread's context
moves the running thread's key. -/
def processOneReplenishmentOnCore (st : SystemState) (execCore : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) : SystemState :=
  markRefillKeyChange st (refillWakeOnCore st execCore scId now) scId

/-- A property the flag write cannot change holds of a replenishment when it holds
of the refill and wake underneath the key hook. -/
theorem processOneReplenishmentOnCore_of_refillWake (P : SystemState → Prop)
    (hFlag : ∀ (s : SystemState) c, P (s.markReschedulePendingOnCore c) = P s)
    {st : SystemState} {execCore : CoreId} {scId : SeLe4n.SchedContextId} {now : Nat}
    (h : P (refillWakeOnCore st execCore scId now)) :
    P (processOneReplenishmentOnCore st execCore scId now) :=
  (markRefillKeyChange_extract_frame P st _ scId hFlag).mpr h

/-- WS-ZA ZA6.2: the compiled `refillWakeOnCore`.  The facts the wake reads off
the refilled state — the target core and whether the store holds the thread —
are read before the wake writes, and the wake is the run-queue placement
`wakeThread` makes (`enqueueRunnableOnCore` at the target), so no state is read
after a later one is built from it and no pair is built for the SGI the flags
now carry (`ZERO_ALLOCATION_SYSCALL_PLAN.md` D1, D2). -/
@[inline] def refillWakeOnCoreImpl (st : SystemState) (execCore : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) : SystemState :=
  let wasExhausted := match st.getSchedContext? scId with
    | some sc => sc.budgetRemaining.isZero
    | none => false
  let refilled := refillSchedContext st scId now
  match (match refilled.getSchedContext? scId with
    | some sc =>
      if wasExhausted && sc.budgetRemaining.isPositive then
        sc.boundThread.filter fun t => (refilled.getTcb? t).any TCB.isRunnable
      else none
    | none => none) with
  | some tid =>
    if runningOnSomeCore refilled tid then refilled
    else
      let target := determineTargetCore refilled tid
      let held := (refilled.getTcb? tid).isSome
      let woken := enqueueRunnableOnCore refilled target tid
      { woken with scheduler := woken.scheduler.markReschedulePendingOnCoreIf target held }
  | none => refilled

theorem refillWakeOnCore_eq_impl (st : SystemState) (execCore : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) :
    refillWakeOnCore st execCore scId now = refillWakeOnCoreImpl st execCore scId now := rfl

/-- WS-ZA ZA6.2: the compiled `processOneReplenishmentOnCore`.  The key hook's
reads of the pre-refill state — the bound thread, its budget eligibility and
its effective key — are taken before the refill writes, so the refill rewrites
the context in its slot and the hook reads only what it was handed
(`markKeyChangeFor`, `markCandidacyGainFor`); the specification's hook reads the
pre-state after the refill. -/
@[inline] def processOneReplenishmentOnCoreImpl (st : SystemState) (execCore : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) : SystemState :=
  match st.getSchedContext? scId with
  | some sc =>
    match sc.boundThread with
    | some t =>
      match st.getTcb? t with
      | some tcb =>
        let preElig := hasSufficientBudget st tcb
        let preDeadline := effectiveDeadline st tcb
        markKeyChangeParts (markCandidacyGainFor (refillWakeOnCoreImpl st execCore scId now) t preElig)
          t tcb.boostedPriority preDeadline tcb.domain
      | none =>
        let post := refillWakeOnCoreImpl st execCore scId now
        markReschedulePendingWhere post
          (fun c => post.queuedOn c t || post.scheduler.currentOnCore c == some t)
          Concurrency.allCores
    | none => refillWakeOnCoreImpl st execCore scId now
  | none => refillWakeOnCoreImpl st execCore scId now

@[csimp] theorem processOneReplenishmentOnCore_eq_impl :
    @processOneReplenishmentOnCore = @processOneReplenishmentOnCoreImpl := by
  funext st execCore scId now
  unfold processOneReplenishmentOnCore processOneReplenishmentOnCoreImpl markRefillKeyChange
    markKeyChangeFrom
  rw [refillWakeOnCore_eq_impl]
  split
  · split
    · rename_i t _
      cases st.getTcb? t with
      | none => rfl
      | some tcb =>
        dsimp only
        rw [markKeyChangeFor_eq_parts, effectiveSchedParams_eq_parts]
    · rfl
  · rfl

/-- WS-ZA ZA6.3: the drain's loop: while core `c`'s release queue has a head
released by `now`, take it, refill it (`processOneReplenishmentOnCore`) and put
it back where its refills now say (`SystemState.releasePlace`: off every queue
when it holds no pending refill, otherwise at its earliest), as seL4-MCS's
`awaken` loop takes the release queue's head while its refill is ready.  At
most `fuel` heads are taken. -/
def drainDueOnCore (c : CoreId) (now : Nat) : Nat → SystemState → SystemState
  | 0, st => st
  | f + 1, st =>
    let h := st.scheduler.releaseHeadOnCore c
    if h = 0 then st
    else if st.releaseAtOn c (ReleaseChain.decode h) ≤ now then
      drainDueOnCore c now f
        ((processOneReplenishmentOnCore st c (ReleaseChain.decode h) now).releasePlace c
          (ReleaseChain.decode h))
    else st

/-- WS-SM SM5.D.4: process **all** of core `c`'s due CBS replenishments at time
`now`: core `c`'s release queue is drained from its head (`drainDueOnCore`),
each due context refilled and placed again by its remaining refills, with the
queue's count as the bound (every context is taken at most once: one put back
holds only refills released after `now`, so it goes behind every due one).
The per-core analogue of `processReplenishmentsDue`, reading / writing core
`c`'s release queue (plus, via the wakes, the target cores' run queues, their
reschedule flags and the object store).  Pure; deterministic; no list is built
(WS-ZA ZA6.3).  What the wakes owe — a `.reschedule` SGI to each remote core
whose flag went up, and the local decision when the executing core's did — is
read off the reschedule flags (WS-ZA ZA6.2). -/
def processReplenishmentsDueOnCore (st : SystemState) (c : CoreId) (now : Nat) :
    SystemState :=
  drainDueOnCore c now (st.scheduler.releaseCountOnCore c) st

/-- WS-ZA ZA6.3: **a property every refill keeps and every re-placement keeps
holds after the drain** — the induction the drain's preservation proofs share,
whatever heads the loop takes and however many. -/
theorem drainDueOnCore_induction (P : SystemState → Prop) (c : CoreId) (now : Nat)
    (hStep : ∀ s scId, P s → P (processOneReplenishmentOnCore s c scId now))
    (hPlace : ∀ s scId, P s → P (s.releasePlace c scId)) :
    ∀ f st, P st → P (drainDueOnCore c now f st)
  | 0, _, h => h
  | f + 1, st, h => by
    unfold drainDueOnCore
    dsimp only
    split
    · exact h
    · split
      · exact drainDueOnCore_induction P c now hStep hPlace f _ (hPlace _ _ (hStep _ _ h))
      · exact h

/-- The re-placement writes the release queues and the contexts' release
fields alone: every other scheduler slot and every thread read the same. -/
@[simp] theorem _root_.SeLe4n.Model.SystemState.releasePlace_runQueueOnCore (s : SystemState)
    (c : CoreId) (scId : SeLe4n.SchedContextId) (c' : CoreId) :
    (s.releasePlace c scId).scheduler.runQueueOnCore c' = s.scheduler.runQueueOnCore c' := by
  rw [(SystemState.releasePlace_releaseOnlyWrite s c scId).2]; rfl

@[simp] theorem _root_.SeLe4n.Model.SystemState.releasePlace_currentOnCore (s : SystemState)
    (c : CoreId) (scId : SeLe4n.SchedContextId) (c' : CoreId) :
    (s.releasePlace c scId).scheduler.currentOnCore c' = s.scheduler.currentOnCore c' := by
  rw [(SystemState.releasePlace_releaseOnlyWrite s c scId).2]; rfl

@[simp] theorem _root_.SeLe4n.Model.SystemState.releasePlace_reschedulePendingOnCore
    (s : SystemState) (c : CoreId) (scId : SeLe4n.SchedContextId) (c' : CoreId) :
    (s.releasePlace c scId).scheduler.reschedulePendingOnCore c' =
      s.scheduler.reschedulePendingOnCore c' := by
  rw [(SystemState.releasePlace_releaseOnlyWrite s c scId).2]; rfl

@[simp] theorem _root_.SeLe4n.Model.SystemState.releasePlace_lastTimeoutErrorsOnCore
    (s : SystemState) (c : CoreId) (scId : SeLe4n.SchedContextId) (c' : CoreId) :
    (s.releasePlace c scId).scheduler.lastTimeoutErrorsOnCore c' =
      s.scheduler.lastTimeoutErrorsOnCore c' := by
  rw [(SystemState.releasePlace_releaseOnlyWrite s c scId).2]; rfl

@[simp] theorem _root_.SeLe4n.Model.SystemState.releasePlace_machine (s : SystemState)
    (c : CoreId) (scId : SeLe4n.SchedContextId) :
    (s.releasePlace c scId).machine = s.machine :=
  (SystemState.releasePlace_releaseOnlyWrite s c scId).machine

theorem _root_.SeLe4n.Model.SystemState.releasePlace_getTcb? (s : SystemState)
    (c : CoreId) (scId : SeLe4n.SchedContextId) (t : SeLe4n.ThreadId) :
    (s.releasePlace c scId).getTcb? t = s.getTcb? t :=
  (SystemState.releasePlace_agree s c scId).getTcb? t

@[simp] theorem _root_.SeLe4n.Model.SystemState.releasePlace_queuedOn (s : SystemState)
    (c : CoreId) (scId : SeLe4n.SchedContextId) (c' : CoreId) (t : SeLe4n.ThreadId) :
    (s.releasePlace c scId).queuedOn c' t = s.queuedOn c' t := by
  unfold SystemState.queuedOn; rw [SystemState.releasePlace_getTcb?]

@[simp] theorem releasePlace_runnableOnSomeCore (s : SystemState) (c : CoreId)
    (scId : SeLe4n.SchedContextId) (t : SeLe4n.ThreadId) :
    runnableOnSomeCore (s.releasePlace c scId) t = runnableOnSomeCore s t := by
  unfold runnableOnSomeCore; simp only [SystemState.releasePlace_queuedOn]

@[simp] theorem releasePlace_placedCoreOf? (s : SystemState) (c : CoreId)
    (scId : SeLe4n.SchedContextId) (t : SeLe4n.ThreadId) :
    placedCoreOf? (s.releasePlace c scId) t = placedCoreOf? s t := by
  unfold placedCoreOf?
  simp only [SystemState.releasePlace_queuedOn, SystemState.releasePlace_currentOnCore]

/-- ...stated over the drain of all of core `c`'s due refills. -/
theorem processReplenishmentsDueOnCore_induction (P : SystemState → Prop) (st : SystemState)
    (c : CoreId) (now : Nat)
    (hStep : ∀ s scId, P s → P (processOneReplenishmentOnCore s c scId now))
    (hPlace : ∀ s scId, P s → P (s.releasePlace c scId)) (h : P st) :
    P (processReplenishmentsDueOnCore st c now) :=
  drainDueOnCore_induction P c now hStep hPlace _ st h

/-- A reading of the state each refill and each re-placement leaves alone is
one the drain leaves alone. -/
theorem processReplenishmentsDueOnCore_frame {α : Type} (f : SystemState → α)
    (st : SystemState) (c : CoreId) (now : Nat)
    (hStep : ∀ (s : SystemState) (scId : SeLe4n.SchedContextId),
      f (processOneReplenishmentOnCore s c scId now) = f s)
    (hPlace : ∀ (s : SystemState) (scId : SeLe4n.SchedContextId),
      f (s.releasePlace c scId) = f s) :
    f (processReplenishmentsDueOnCore st c now) = f st :=
  processReplenishmentsDueOnCore_induction (fun s => f s = f st) st c now
    (fun s scId h => (hStep s scId).trans h) (fun s scId h => (hPlace s scId).trans h) rfl

/-- WS-SM SM5.H.2 (plan §3.8): schedule SchedContext `scId`'s CBS
replenishment on core `c` — put it on core `c`'s release queue at its earliest
pending refill (`SystemState.releasePlace`, WS-ZA ZA6.3), off whichever queue
held it before, as seL4-MCS's `postpone` re-places a context whose budget ran
out.  The named CBS-replenishment-scheduling primitive that the live per-core
budget tick (`timerTickBudgetOnCore`, below) **calls** for its replenishment
write.  Defined here, before the tick, to satisfy the forward reference. -/
def replenishOnCore (st : SystemState) (c : CoreId) (scId : SchedContextId) : SystemState :=
  st.releasePlace c scId

/-- WS-ZA ZA4.3: an unbound thread's time slice ends on core `c`: the slice is
reset to `configDefaultTimeSlice` and `tid` goes to the back of its priority
band on core `c`'s run queue.  The timer tick's unbound arm when the slice runs
out, and the yield syscall's unbound arm (`yieldChargeOnCore`): one definition,
so a yield and an expired slice cannot come to disagree. -/
@[inline] def sliceExpireOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) : SystemState :=
  let tcb' := { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }
  let st' := st.rewriteObject tid.toObjId (.tcb tcb')
    (SystemState.rewriteAdmissible_tcb hTcb tcb')
  st'.runEnqueueOnCore c tid tcb.boostedPriority

/-- WS-ZA ZA4.3: a bound thread's budget is spent on core `c`: `ticks` run from
`start` are charged against SchedContext `scId` (the timer tick charges the unit
just run to a head it uses up; the yield syscall charges the whole head,
`seL4_Yield` under MCS).  WS-ZA ZA6.4: the charge is seL4-MCS's
(`SchedContext.chargeBudget`: `refill_unblock_check` at the run's start,
`refill_budget_check` with `schedule_used`, then the release of a pending refill
already due), so the budget is conserved and the used head is released again one
period after its release.  The CBS deadline moves, the context goes on core
`c`'s release queue at its place (`replenishOnCore`, seL4-MCS's `postpone`), and
`tid` is re-enqueued on core `c` at its insert priority (ineligible until the
release).  The part of the timer tick's exhausted arm that the yield syscall
shares; the tick then times out the SchedContext's IPC-blocked threads
(`budgetExhaustOnCore`). -/
@[inline] def spendBudgetOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (scId : SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (start ticks : Nat) : SystemState :=
  let now := st.machine.timer
  let sc''' := cbsUpdateDeadline (sc.chargeBudget start ticks now) now true
  let st' := st.rewriteObject scId.toObjId (.schedContext sc''')
    (SystemState.rewriteAdmissible_schedContext hSc sc''')
  -- WS-SM SM5.H.2: schedule the CBS replenishment via the named primitive
  -- `replenishOnCore`: the context goes on core `c`'s release queue at its
  -- place, its first pending refill's release (WS-ZA ZA6.3, ZA6.4).
  let stReplenished := replenishOnCore st' c scId
  stReplenished.runEnqueueOnCore c tid (resolveInsertPriority st' tid sc)

/-- WS-ZA ZA4.3: the compiled `sliceExpireOnCore`.  The TCB is written in its
slot (`modifyObject`), so a state the caller owns has neither the TCB nor the
object table rebuilt; proven equal to the specification
(`sliceExpireOnCore_eq_impl`). -/
@[inline] def sliceExpireOnCoreImpl (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (_hTcb : st.getTcb? tid = some tcb) : SystemState :=
  let slice := st.scheduler.configDefaultTimeSlice
  let st' := st.modifyObject tid.toObjId (SystemState.mapTcbObject fun t => { t with timeSlice := slice })
  st'.runEnqueueOnCore c tid tcb.boostedPriority

@[csimp] theorem sliceExpireOnCore_eq_impl : @sliceExpireOnCore = @sliceExpireOnCoreImpl := by
  funext st c tid tcb hTcb
  have hx := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  unfold sliceExpireOnCore sliceExpireOnCoreImpl SystemState.modifyObject
    SystemState.rewriteObject
  simp only [RobinHood.RHTable.modify_of_get? hx]
  rfl

/-- WS-ZA ZA6.3: the context a charge writes back: `ticks` run from `start`
charged by `now` (`SchedContext.chargeBudget`, WS-ZA ZA6.4), the deadline rule
applied.  A call, so the slot's rewrite is one straight-line write of the object
it holds and reuses that object's cell. -/
@[noinline] def chargeSchedContext (s : SchedContext) (start ticks now : Nat) : SchedContext :=
  cbsUpdateDeadline (s.chargeBudget start ticks now) now true

/-- WS-ZA ZA6.3: the priority a thread is re-enqueued at: its boosted priority
(`resolveEffectivePrioDeadline_fst_eq_boostedPriority`), or `fallback` when the
store holds no thread under `tid`.  Read as one number, with no pair built for
the deadline the insert does not read. -/
@[noinline] def insertPriorityOf (st : SystemState) (tid : SeLe4n.ThreadId)
    (fallback : SeLe4n.Priority) : SeLe4n.Priority :=
  match st.getTcb? tid with
  | some tcb => tcb.boostedPriority
  | none => fallback

theorem resolveInsertPriority_eq_insertPriorityOf (st : SystemState) (tid : SeLe4n.ThreadId)
    (sc : SchedContext) : resolveInsertPriority st tid sc = insertPriorityOf st tid sc.priority := by
  unfold resolveInsertPriority insertPriorityOf
  cases st.getTcb? tid with
  | none => rfl
  | some tcb => exact resolveEffectivePrioDeadline_fst_eq_boostedPriority st tcb

/-- WS-ZA ZA6.3: the budget spend's writes, handed the charge (`ticks` from
`start`) and the fallback priority read off the context: the context rewritten
in its slot (`chargeSchedContext`), placed on core `c`'s release queue
(`replenishOnCore`) and `tid` re-enqueued.  A call, so the caller's context is
not held across the rewrite of its slot. -/
@[noinline] def spendBudgetWrite (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (scId : SchedContextId) (start ticks : Nat) (fallback : SeLe4n.Priority) : SystemState :=
  let now := st.machine.timer
  let st' := st.modifyObject scId.toObjId (SystemState.mapSchedContextObject fun s =>
    chargeSchedContext s start ticks now)
  let prio := insertPriorityOf st' tid fallback
  (replenishOnCore st' c scId).runEnqueueOnCore c tid prio

/-- WS-ZA ZA4.3: the compiled `spendBudgetOnCore`.  The SchedContext is written
in its slot, and the insert priority is read off the state before the refill
is queued on it, so no state is read after a later one is built from it
(`ZERO_ALLOCATION_SYSCALL_PLAN.md` D1).  WS-ZA ZA6.3: the writes are one call
(`spendBudgetWrite`) handed the numbers they read off the context, so the
context the caller looked up is released before its slot is rewritten.
Proven equal to the specification (`spendBudgetOnCore_eq_impl`). -/
@[inline] def spendBudgetOnCoreImpl (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (scId : SchedContextId) (sc : SchedContext)
    (_hSc : st.getSchedContext? scId = some sc) (start ticks : Nat) : SystemState :=
  spendBudgetWrite st c tid scId start ticks sc.priority

@[csimp] theorem spendBudgetOnCore_eq_impl : @spendBudgetOnCore = @spendBudgetOnCoreImpl := by
  funext st c tid scId sc hSc start ticks
  have hx := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSc
  unfold spendBudgetOnCore spendBudgetOnCoreImpl spendBudgetWrite chargeSchedContext
    SystemState.modifyObject SystemState.rewriteObject
  simp only [RobinHood.RHTable.modify_of_get? hx]
  rw [resolveInsertPriority_eq_insertPriorityOf]
  rfl

/-- The slice expiry keeps the object table's invariant: the slice reset is an
in-place rewrite and the enqueue writes run-queue links in place (WS-ZA ZA4.5). -/
theorem sliceExpireOnCore_objects_invExt (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt) :
    (sliceExpireOnCore st c tid tcb hTcb).objects.invExt :=
  SystemState.runEnqueueOnCore_objects_invExt _ c tid _
    (SystemState.rewriteObject_preserves_objects_invExt st _ _
      (SystemState.rewriteAdmissible_tcb hTcb _) hObjInv)

/-- The budget spend keeps the object table's invariant: the SchedContext write
is in place, the refill is a scheduler write, and the enqueue writes run-queue
links in place (WS-ZA ZA4.5). -/
theorem spendBudgetOnCore_objects_invExt (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (scId : SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (start ticks : Nat)
    (hObjInv : st.objects.invExt) :
    (spendBudgetOnCore st c tid scId sc hSc start ticks).objects.invExt :=

  SystemState.runEnqueueOnCore_objects_invExt _ c tid _
    (SystemState.releasePlace_objects_invExt _ c scId
      (SystemState.rewriteObject_preserves_objects_invExt st _ _
        (SystemState.rewriteAdmissible_schedContext hSc _) hObjInv))

/-- Mark the reschedule flag of every core an SGI list names: the cores a
step's wakes owe a scheduling point, recorded where the step's seam reads them
(`rescheduleSgisFromFlags`, WS-ZA ZA6.2). -/
def markRescheduleTargets (s : SchedulerState) : List (CoreId × SgiKind) → SchedulerState
  | [] => s
  | p :: ps => markRescheduleTargets (s.markReschedulePendingOnCore p.1) ps

/-- The marks write the reschedule flags alone. -/
theorem markRescheduleTargets_eq (s : SchedulerState) (l : List (CoreId × SgiKind)) :
    markRescheduleTargets s l = { s with reschedulePending := (markRescheduleTargets s l).reschedulePending } := by
  induction l generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [markRescheduleTargets]
    rw [ih]
    rfl

@[simp] theorem markRescheduleTargets_currentOnCore (s : SchedulerState) (l : List (CoreId × SgiKind)) (c' : CoreId) :
    (markRescheduleTargets s l).currentOnCore c' = s.currentOnCore c' := by
  rw [markRescheduleTargets_eq]; rfl

@[simp] theorem markRescheduleTargets_runQueueOnCore (s : SchedulerState) (l : List (CoreId × SgiKind)) (c' : CoreId) :
    (markRescheduleTargets s l).runQueueOnCore c' = s.runQueueOnCore c' := by
  rw [markRescheduleTargets_eq]; rfl

@[simp] theorem markRescheduleTargets_runQueueEndsOnCore (s : SchedulerState) (l : List (CoreId × SgiKind)) (c' : CoreId) :
    (markRescheduleTargets s l).runQueueEndsOnCore c' = s.runQueueEndsOnCore c' := by
  rw [markRescheduleTargets_eq]; rfl

@[simp] theorem markRescheduleTargets_replenishQueueOnCore (s : SchedulerState) (l : List (CoreId × SgiKind)) (c' : CoreId) :
    (markRescheduleTargets s l).replenishQueueOnCore c' = s.replenishQueueOnCore c' := by
  rw [markRescheduleTargets_eq]; rfl

@[simp] theorem markRescheduleTargets_activeDomainOnCore (s : SchedulerState) (l : List (CoreId × SgiKind)) (c' : CoreId) :
    (markRescheduleTargets s l).activeDomainOnCore c' = s.activeDomainOnCore c' := by
  rw [markRescheduleTargets_eq]; rfl

@[simp] theorem markRescheduleTargets_domainTimeRemainingOnCore (s : SchedulerState) (l : List (CoreId × SgiKind)) (c' : CoreId) :
    (markRescheduleTargets s l).domainTimeRemainingOnCore c' = s.domainTimeRemainingOnCore c' := by
  rw [markRescheduleTargets_eq]; rfl

@[simp] theorem markRescheduleTargets_domainScheduleIndexOnCore (s : SchedulerState) (l : List (CoreId × SgiKind)) (c' : CoreId) :
    (markRescheduleTargets s l).domainScheduleIndexOnCore c' = s.domainScheduleIndexOnCore c' := by
  rw [markRescheduleTargets_eq]; rfl

@[simp] theorem markRescheduleTargets_lastTimeoutErrorsOnCore (s : SchedulerState) (l : List (CoreId × SgiKind)) (c' : CoreId) :
    (markRescheduleTargets s l).lastTimeoutErrorsOnCore c' = s.lastTimeoutErrorsOnCore c' := by
  rw [markRescheduleTargets_eq]; rfl

@[simp] theorem markRescheduleTargets_domainSchedule (s : SchedulerState) (l : List (CoreId × SgiKind)) :
    (markRescheduleTargets s l).domainSchedule = s.domainSchedule := by
  rw [markRescheduleTargets_eq]

@[simp] theorem markRescheduleTargets_configDefaultTimeSlice (s : SchedulerState) (l : List (CoreId × SgiKind)) :
    (markRescheduleTargets s l).configDefaultTimeSlice = s.configDefaultTimeSlice := by
  rw [markRescheduleTargets_eq]

/-- The marks lower no flag. -/
theorem markRescheduleTargets_reschedulePendingOnCore_mono (s : SchedulerState)
    (l : List (CoreId × SgiKind)) (d : CoreId) (h : s.reschedulePendingOnCore d = true) :
    (markRescheduleTargets s l).reschedulePendingOnCore d = true := by
  induction l generalizing s with
  | nil => exact h
  | cons p ps ih =>
    apply ih
    by_cases hd : p.1 = d
    · subst hd; simp
    · rw [SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_ne _ _ _ hd]; exact h

/-- Every core the list names is flagged. -/
theorem markRescheduleTargets_marks (s : SchedulerState) (l : List (CoreId × SgiKind))
    (p : CoreId × SgiKind) (hp : p ∈ l) :
    (markRescheduleTargets s l).reschedulePendingOnCore p.1 = true := by
  induction l generalizing s with
  | nil => cases hp
  | cons q qs ih =>
    simp only [markRescheduleTargets]
    rcases List.mem_cons.mp hp with h | h
    · subst h
      exact markRescheduleTargets_reschedulePendingOnCore_mono _ _ _ (by simp)
    · exact ih _ h

/-- A bound thread's budget runs out on the timer tick: the budget is spent
(`spendBudgetOnCore`) under the thread's key hook (`markKeyChangeFor` against
`preKey`, its key before the spend — the spend moves the context's deadline),
and the IPC-blocked threads the SchedContext bounded time out, their errors
recorded in core `c`'s `lastTimeoutErrorsOnCore` diagnostic and each woken
thread's home core flagged (`markRescheduleTargets`), so its `.reschedule` SGI is
read off the flags (WS-ZA ZA6.2).  The hook is the yield's
(`yieldChargeOnCore`), so the two exhausting charges answer the coverage
question alike. -/
@[inline] def budgetExhaustOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (preKey : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId)
    (scId : SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (ticks : Nat) : SystemState :=
  -- PR #880 round 8: timeout wakes land on each thread's HOME core.
  let timedOut := timeoutBlockedThreads
    (markKeyChangeFor (spendBudgetOnCore st c tid scId sc hSc (st.machine.timer - ticks) ticks) tid preKey) scId c
  { timedOut.1 with scheduler := (markRescheduleTargets
      (timedOut.1.scheduler.setLastTimeoutErrorsOnCore c timedOut.2.1) timedOut.2.2) }

/-- WS-ZA ZA6.2: the timeout pass has nothing to do: the context names no
thread the store holds blocked on IPC (`tcbBlockingInfo`), so the pass records
no error and owes no wake (`timeoutBlockedThreads_of_quiet`). -/
@[inline] def timeoutPassQuiet (st : SystemState) (scId : SchedContextId) : Bool :=
  match st.getSchedContext? scId with
  | some sc =>
    match sc.boundThread with
    | some t =>
      match st.getTcb? t with
      | some tcb => (tcbBlockingInfo tcb).isNone
      | none => true
    | none => true
  | none => true

theorem timeoutBlockedThreads_of_quiet {st : SystemState} {scId : SchedContextId}
    (h : timeoutPassQuiet st scId = true) (execCore : CoreId) :
    timeoutBlockedThreads st scId execCore = (st, [], []) := by
  unfold timeoutPassQuiet at h
  unfold timeoutBlockedThreads
  split
  · rename_i sc hS
    rw [hS] at h; dsimp only at h
    split
    · rename_i t hB
      rw [hB] at h; dsimp only at h
      unfold timeoutBlockedThreadStep
      dsimp only
      cases hT : st.getTcb? t with
      | none => rfl
      | some tcb =>
        rw [hT] at h; dsimp only at h
        cases hI : tcbBlockingInfo tcb with
        | none => simp only [hI]
        | some _ => rw [hI] at h; cases h
    · rfl
  · rfl

/-- WS-ZA ZA6.2: the compiled `budgetExhaustOnCore`.  The timeout pass visits
the context's one bound thread and times it out only when it is blocked on IPC;
on every other path (`timeoutPassQuiet`) it records no error and owes no wake,
so the diagnostic is cleared in its slot with no triple built for the pass's
result.  A bound thread blocked on IPC runs the specification. -/
@[inline] def budgetExhaustOnCoreImpl (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (preKey : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId)
    (scId : SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (ticks : Nat) : SystemState :=
  let spent := markKeyChangeFor (spendBudgetOnCore st c tid scId sc hSc (st.machine.timer - ticks) ticks) tid preKey
  if timeoutPassQuiet spent scId then
    { spent with scheduler := spent.scheduler.setLastTimeoutErrorsOnCore c [] }
  else
    let timedOut := timeoutBlockedThreads spent scId c
    { timedOut.1 with scheduler := (markRescheduleTargets
        (timedOut.1.scheduler.setLastTimeoutErrorsOnCore c timedOut.2.1) timedOut.2.2) }

@[csimp] theorem budgetExhaustOnCore_eq_impl :
    @budgetExhaustOnCore = @budgetExhaustOnCoreImpl := by
  funext st c tid preKey scId sc hSc ticks
  unfold budgetExhaustOnCore budgetExhaustOnCoreImpl
  dsimp only
  split
  · rename_i hQ
    rw [timeoutBlockedThreads_of_quiet hQ]
    rfl
  · rfl

/-- WS-SM SM5.D.5 (per-core budget/time-slice tick): the per-core analogue of
`timerTickBudget`.  Charges the current thread `tid` (with TCB `tcb`) one tick of
budget on core `c`, returning `(updatedState, wasPreempted)`.

Dispatches on `tcb.schedContextBinding` exactly as `timerTickBudget`:
- **Unbound, time-slice > 1**: decrement `timeSlice`; no preemption.
- **Unbound, time-slice ≤ 1**: reset `timeSlice` to `configDefaultTimeSlice`,
  re-enqueue `tid` into core `c`'s run queue at `TCB.boostedPriority`,
  signal preemption.
- **Bound, head not used up** (`SchedContext.tickExhausts`): charge the unit
  just run (`SchedContext.chargeBudget`, WS-ZA ZA6.4); no preemption.
- **Bound, head used up**: budget exhausted — charge it, put the context on
  core `c`'s release queue at its place, re-enqueue `tid` into core `c`'s run queue,
  run `tid`'s key hook against its key before the spend, time out any IPC-blocked threads the SC bounded (recording errors in core `c`'s
  `lastTimeoutErrorsOnCore` diagnostic, flagging each woken thread's home core),
  signal preemption.
- **Bound, SC missing**: charged nothing, as an idle core is (WS-ZA ZA6.2: the
  tick is total, as seL4's `timerTick` is; the arm is unreachable under
  `schedContextStoreConsistent`, which the theorems that need the charge consume).

Reads / writes core `c`'s scheduler slots (`runQueueOnCore c`,
`replenishQueueOnCore c`, `lastTimeoutErrorsOnCore c`), the object store, and —
via the round-8 target-aware timeout wakes — the woken threads' home-core run
queues and reschedule flags.

**No `machine.timer` advance** (unlike `timerTickBudget`): the per-core tick is
read-only w.r.t. the shared global tick counter (see the SM5.D section header —
global-timer ownership). -/
def timerTickBudgetOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) : SystemState × Bool :=
  match tcb.schedContextBinding with
  | .unbound =>
    if tcb.timeSlice ≤ 1 then
      (sliceExpireOnCore st c tid tcb hTcb, true)
    else
      let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
      (st.rewriteObject tid.toObjId (.tcb tcb')
         (SystemState.rewriteAdmissible_tcb hTcb tcb'), false)
  | .bound scId | .donated scId _ =>
    match st.getSchedContextWitnessed? scId with
    | some ⟨sc, hSc⟩ =>
      let now := st.machine.timer
      if sc.tickExhausts (now - 1) then
        (budgetExhaustOnCore st c tid (effectiveSchedParams st tcb) scId sc hSc 1, true)
      else
        let sc' := sc.chargeBudget (now - 1) 1 now
        (st.rewriteObject scId.toObjId (.schedContext sc')
          (SystemState.rewriteAdmissible_schedContext hSc sc'), false)
    | none => (st, false)

/-- WS-ZA ZA6.2: the compiled `timerTickBudgetOnCore`.  The two arms that
decrement a counter write it in its slot (`modifyObject`) rather than
re-inserting a copy of the object, so the store is updated in place. -/
@[inline] def timerTickBudgetOnCoreImpl (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) : SystemState × Bool :=
  match tcb.schedContextBinding with
  | .unbound =>
    if tcb.timeSlice ≤ 1 then
      (sliceExpireOnCore st c tid tcb hTcb, true)
    else
      (st.modifyObject tid.toObjId
        (SystemState.mapTcbObject fun t => { t with timeSlice := t.timeSlice - 1 }), false)
  | .bound scId | .donated scId _ =>
    match st.getSchedContextWitnessed? scId with
    | some ⟨sc, hSc⟩ =>
      let now := st.machine.timer
      if sc.tickExhausts (now - 1) then
        (budgetExhaustOnCore st c tid (tcb.boostedPriority, effectiveDeadline st tcb, tcb.domain)
          scId sc hSc 1, true)
      else
        (st.modifyObject scId.toObjId
          (SystemState.mapSchedContextObject fun s => s.chargeBudget (now - 1) 1 now), false)
    | none => (st, false)

@[csimp] theorem timerTickBudgetOnCore_eq_impl :
    @timerTickBudgetOnCore = @timerTickBudgetOnCoreImpl := by
  funext st c tid tcb hTcb
  have hx := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  unfold timerTickBudgetOnCore timerTickBudgetOnCoreImpl
  cases hB : tcb.schedContextBinding with
  | unbound =>
    by_cases hS : tcb.timeSlice ≤ 1
    · simp only [hS, ↓reduceIte]
    · simp only [hS, ↓reduceIte, SystemState.modifyObject, SystemState.rewriteObject]
      rw [RobinHood.RHTable.modify_of_get? hx]
      rfl
  | bound scId =>
    cases hS : st.getSchedContext? scId with
    | none => simp only [SystemState.getSchedContextWitnessed?_eq_none hS]
    | some sc =>
      have hy := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hS
      simp only [SystemState.getSchedContextWitnessed?_eq_some hS]
      cases hBud : sc.tickExhausts (st.machine.timer - 1)
      · simp only [hBud, Bool.false_eq_true, ↓reduceIte, SystemState.modifyObject,
          SystemState.rewriteObject]
        rw [RobinHood.RHTable.modify_of_get? hy]
        rfl
      · simp only [hBud, ↓reduceIte, effectiveSchedParams_eq_parts]
  | donated scId o =>
    cases hS : st.getSchedContext? scId with
    | none => simp only [SystemState.getSchedContextWitnessed?_eq_none hS]
    | some sc =>
      have hy := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hS
      simp only [SystemState.getSchedContextWitnessed?_eq_some hS]
      cases hBud : sc.tickExhausts (st.machine.timer - 1)
      · simp only [hBud, Bool.false_eq_true, ↓reduceIte, SystemState.modifyObject,
          SystemState.rewriteObject]
        rw [RobinHood.RHTable.modify_of_get? hy]
        rfl
      · simp only [hBud, ↓reduceIte, effectiveSchedParams_eq_parts]

/-- WS-SM SM5.D.5 (raw-write migration Cut B2): charge core `c`'s current thread
`tid` one tick, **resolved from the store** — the witnessed lookup
`getTcbWitnessed?` supplies `timerTickBudgetOnCore` the proof its in-place rewrite
consumes.  A current thread the store does not hold is charged nothing, as an
idle core is (WS-ZA ZA6.2: the tick is total, as seL4's `timerTick` is; the arm
is unreachable under `currentThreadValidOnCore`, which the theorems that need
the charge consume).

**Why this is a definition rather than the tick's own `match`.**  The lookup is a
*dependent* match — the `some ⟨tcb, hTcb⟩` alternative's type names the state
scrutinised — and over a `have`-bound state or a stuck projection such as
`(timerTickOnCorePrepared st c)` a dependent match is opaque to definitional
unification, so `timerTickOnCore_eq_prepared` (`rfl`) would stop elaborating
with the lookup inline.  Over a **parameter** the match is ordinary.  The frame
every consumer reads is `timerTickChargeCurrentOnCore_eq`: the charge at a
resolving thread is `timerTickBudgetOnCore` at the witnessed TCB. -/
@[inline] def timerTickChargeCurrentOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    SystemState × Bool :=
  match st.getTcbWitnessed? tid with
  | some ⟨tcb, hTcb⟩ => timerTickBudgetOnCore st c tid tcb hTcb
  | none => (st, false)

/-- The charge at a resolving thread is the budget tick at its TCB. -/
theorem timerTickChargeCurrentOnCore_eq {st : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hTcb : st.getTcb? tid = some tcb) :
    timerTickChargeCurrentOnCore st c tid = timerTickBudgetOnCore st c tid tcb hTcb := by
  unfold timerTickChargeCurrentOnCore
  rw [SystemState.getTcbWitnessed?_eq_some hTcb]

/-- A thread the store does not hold is charged nothing. -/
theorem timerTickChargeCurrentOnCore_none {st : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId} (hNone : st.getTcb? tid = none) :
    timerTickChargeCurrentOnCore st c tid = (st, false) := by
  unfold timerTickChargeCurrentOnCore
  rw [SystemState.getTcbWitnessed?_eq_none hNone]

/-- Core `c`'s scheduling point after its tick's charge: the local reschedule
decision (`handleRescheduleOnCoreState`) when core `c`'s reschedule flag is up,
the state as it is otherwise.  The flag is what the drain's wakes and the
charge's timeout wakes raise on the core whose decision they staled
(WS-ZA ZA6.2), and a decision clears it. -/
@[inline] def rescheduleIfPendingOnCore (st : SystemState) (c : CoreId) : SystemState :=
  if st.scheduler.reschedulePendingOnCore c then handleRescheduleOnCoreState st c else st

/-- WS-SM SM5.D.2 (plan §3.4): the per-core timer tick — the full per-core
analogue of `timerTickWithBudget`.  Total, as seL4's `timerTick` is (WS-ZA ZA6.2).

Processing order (on core `c`, at the current global time `now := machine.timer`,
which the tick reads but does not advance — see the SM5.D section header):
1. **SM5.D.9**: clear core `c`'s `lastTimeoutErrorsOnCore` diagnostic, so a stale
   timeout-error record never survives across rounds.
2. **SM5.D.4**: process core `c`'s due CBS replenishments
   (`processReplenishmentsDueOnCore`); each wake flags the core whose decision
   it staled.
3. **SM5.D.5**: charge the running thread one tick (`timerTickBudgetOnCore`); if
   that exhausts its budget / time-slice (preemption), re-select and dispatch the
   highest-priority budget-eligible runnable thread on core `c`
   (`scheduleEffectiveOnCoreState`).  An idle core (`currentOnCore c = none`), a
   current thread the store does not hold and a bound context the store does
   not hold are charged nothing.
4. **Local reschedule** (PR #880 round 7, read off the flag since ZA6.2): when
   step 3 did not re-dispatch and core `c`'s reschedule flag is up — a drain
   wake landed on core `c` itself, or an earlier entry staled its decision —
   run the receiver-side reschedule decision locally
   (`handleRescheduleOnCoreState`: switch only if the best candidate outranks
   the current thread in the selector's own order).  No SGI can poke the core
   executing the tick, so without this decision a refilled higher-priority
   thread already queued on core `c` waited out the current thread's entire
   remaining budget.  The idle arm runs the same decision: a vacated core whose
   queued thread was ineligible at vacate time is dispatched the moment its
   refill lands.

The tick does **budget accounting only** and never writes
`domainTimeRemainingOnCore` (audit-pass-2 domain-rotation faithfulness, mirroring
single-core `timerTickWithBudget`); per-core *domain* rotation is the separate
atomic `scheduleDomainOnCore`.

Returns the post-tick state.  The cross-core `.reschedule` SGIs the tick owes
are the remote cores whose reschedule flag it raised; the run-loop step reads
them off the flags (`perCoreTimerTickStep`), as the syscall seam does, and the
runtime ISR (SM5.D.1) fires them after the state write is visible. -/
def timerTickOnCore (st : SystemState) (c : CoreId) : SystemState :=
  -- SM5.D.9: clear core c's timeout-error diagnostic at tick entry.
  let st0 := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] }
  -- SM5.D.4: process core c's due CBS replenishments (+ cross-core wakes).
  let st1 := processReplenishmentsDueOnCore st0 c st0.machine.timer
  -- SM5.D.5: per-core budget/time-slice tick + local preemption.  The tick does
  -- **budget accounting only** (audit-pass-2): rotation folded into the tick
  -- left a running thread outside the rotated domain; the run loop invokes
  -- `timerTickOnCore` then `scheduleDomainOnCore`, as the single-core loop
  -- invokes `timerTickWithBudget` then `scheduleDomain`.
  match st1.scheduler.currentOnCore c with
  | none => rescheduleIfPendingOnCore st1 c
  | some tid =>
      match timerTickChargeCurrentOnCore st1 c tid with
      | (st2, true) => scheduleEffectiveOnCoreState st2 c
      | (st2, false) => rescheduleIfPendingOnCore st2 c

-- ── the prepared state + the `timerTickOnCore` characterisation ──

/-- WS-SM SM5.D.2: the state `timerTickOnCore` reaches after the SM5.D.9 clear +
SM5.D.4 replenishment, **before** the SM5.D.5 budget tick / preemption.
Audit-pass-2: the tick does **no** in-tick domain accounting (rotation is the
separate `scheduleDomainOnCore`), so the prepared state is exactly the
post-replenishment state.  Naming it lets the SM5.D headline theorems
characterise `timerTickOnCore`'s behaviour without restating its internal
`let`-chain.  Since WS-ZA ZA6.2 the drain's wakes report through the
reschedule flags, so the prepared state is the whole of what the drain hands
the charge. -/
def timerTickOnCorePrepared (st : SystemState) (c : CoreId) : SystemState :=
  let st0 := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] }
  processReplenishmentsDueOnCore st0 c st0.machine.timer

/-- WS-SM SM5.D.2: `timerTickOnCore` is the SM5.D.5 budget tick / preemption —
plus the local reschedule decision — dispatched on the SM5.D.2/.4 prepared
state.  `rfl` — the production `let`-chain *is* this composition.  Every SM5.D.2
headline below is a corollary.  The charge is the named step
`timerTickChargeCurrentOnCore` (raw-write migration Cut B2): its witnessed lookup
is a *dependent* match, and one of those inline over the stuck application
`timerTickOnCorePrepared st c` is opaque to definitional unification; a consumer
reaches the budget tick through `timerTickChargeCurrentOnCore_eq hTcb`. -/
theorem timerTickOnCore_eq_prepared (st : SystemState) (c : CoreId) :
    timerTickOnCore st c =
      (match (timerTickOnCorePrepared st c).scheduler.currentOnCore c with
       | none => rescheduleIfPendingOnCore (timerTickOnCorePrepared st c) c
       | some tid =>
           match timerTickChargeCurrentOnCore (timerTickOnCorePrepared st c) c tid with
           | (st2, true) => scheduleEffectiveOnCoreState st2 c
           | (st2, false) => rescheduleIfPendingOnCore st2 c) := rfl

/-- WS-ZA ZA6.2: the tick's four outcomes.  An idle core, and a current thread
the store does not hold, end in the local decision on the prepared state; a
charge that preempts ends in the dispatch; one that does not ends in the local
decision on the charged state.  The theorems over the tick case on this. -/
theorem timerTickOnCore_cases (st : SystemState) (c : CoreId) :
    ((timerTickOnCorePrepared st c).scheduler.currentOnCore c = none ∧
        timerTickOnCore st c = rescheduleIfPendingOnCore (timerTickOnCorePrepared st c) c) ∨
    (∃ tid, (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid ∧
        (timerTickOnCorePrepared st c).getTcb? tid = none ∧
        timerTickOnCore st c = rescheduleIfPendingOnCore (timerTickOnCorePrepared st c) c) ∨
    (∃ tid tcb, ∃ hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb, ∃ st3,
        (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid ∧
        timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, true) ∧
        timerTickOnCore st c = scheduleEffectiveOnCoreState st3 c) ∨
    (∃ tid tcb, ∃ hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb, ∃ st3,
        (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid ∧
        timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, false) ∧
        timerTickOnCore st c = rescheduleIfPendingOnCore st3 c) := by
  rw [timerTickOnCore_eq_prepared]
  cases hCur : (timerTickOnCorePrepared st c).scheduler.currentOnCore c with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some tid =>
    cases hTcb : (timerTickOnCorePrepared st c).getTcb? tid with
    | none =>
      refine Or.inr (Or.inl ⟨tid, rfl, hTcb, ?_⟩)
      simp only [timerTickChargeCurrentOnCore_none hTcb]
    | some tcb =>
      simp only [timerTickChargeCurrentOnCore_eq hTcb]
      cases hB : timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb with
      | mk st3 b =>
        cases b
        · exact Or.inr (Or.inr (Or.inr ⟨tid, tcb, hTcb, st3, rfl, hB, rfl⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨tid, tcb, hTcb, st3, rfl, hB, rfl⟩))

/-- The local decision keeps whatever the state and the decision both keep. -/
theorem rescheduleIfPendingOnCore_of {P : SystemState → Prop} (st : SystemState) (c : CoreId)
    (h : P st) (h' : P (handleRescheduleOnCoreState st c)) :
    P (rescheduleIfPendingOnCore st c) := by
  unfold rescheduleIfPendingOnCore; split
  · exact h'
  · exact h

/-- The tick keeps whatever the prepared state has, the local decision and the
dispatch both keep, and every budget tick at the prepared state's current thread
establishes.  The theorems whose fact every phase carries alike lift through
this. -/
theorem timerTickOnCore_of {P : SystemState → Prop} (st : SystemState) (c : CoreId)
    (hPrep : P (timerTickOnCorePrepared st c))
    (hR : ∀ s, P s → P (handleRescheduleOnCoreState s c))
    (hS : ∀ s, P s → P (scheduleEffectiveOnCoreState s c))
    (hB : ∀ tid tcb (hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb) st3 b,
      timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, b) → P st3) :
    P (timerTickOnCore st c) := by
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, _, hb, h⟩ |
      ⟨tid, tcb, hTcb, st3, _, hb, h⟩ <;> rw [h]
  · exact rescheduleIfPendingOnCore_of _ c hPrep (hR _ hPrep)
  · exact rescheduleIfPendingOnCore_of _ c hPrep (hR _ hPrep)
  · exact hS _ (hB tid tcb hTcb st3 true hb)
  · have h3 := hB tid tcb hTcb st3 false hb
    exact rescheduleIfPendingOnCore_of _ c h3 (hR _ h3)

/-- WS-ZA ZA4.3: charge a yield to `tid`, current on core `c`.  Yield forfeits
what is left of the caller's allotment (decided 2026-10-11; `seL4_Yield` under
MCS): a thread bound to a SchedContext gives up its remaining budget until the
release (`spendBudgetOnCore`, charging the whole head refill from now), and an
unbound thread ends its time slice (`sliceExpireOnCore`).  Both are shared with
the timer tick's exhausted arms.

The forfeit times out no IPC: the tick's timeout pass is not run.  A server
yielding on a client's donated budget leaves the client's call standing, as
`seL4_Yield` raises no timeout fault; only a budget that runs out on the timer
aborts the calls it bounded.  The bound arm ends in the SchedContext's key hook
(`markKeyChangeFor`): the deadline it moves is the caller's key, so every core
whose decision the moved key stales is flagged, as every key writer on the
syscall path ends.

A definition over a parameter thread, like `timerTickChargeCurrentOnCore`, so
the witnessed lookup's dependent match stays out of `yieldOnCore`'s match tree. -/
def yieldChargeOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    Except KernelError SystemState :=
  match st.getTcbWitnessed? tid with
  | none => .error .schedulerInvariantViolation
  | some ⟨tcb, hTcb⟩ =>
    match tcb.schedContextBinding with
    | .unbound => .ok (sliceExpireOnCore st c tid tcb hTcb)
    | .bound scId | .donated scId _ =>
      match st.getSchedContextWitnessed? scId with
      | some ⟨sc, hSc⟩ =>
        .ok (markKeyChangeFor (spendBudgetOnCore st c tid scId sc hSc st.machine.timer sc.budget.val)
          tid (effectiveSchedParams st tcb))
      -- R5.E fail-closed, as the tick: unreachable under
      -- `schedContextStoreConsistent`.
      | none => .error .missingSchedContext

/-- WS-ZA ZA4.3: the yield syscall on the executing core `c` (`SyscallId.yield`).
The caller, `currentOnCore c`, forfeits its allotment (`yieldChargeOnCore`) and
core `c` re-selects (`scheduleEffectiveOnCore`), the same pairing as a tick that
preempts.  A bound caller with no budget left is ineligible until its refill,
so a lower-priority thread runs; an unbound caller is behind every
equal-priority thread already queued, and runs again at once only if it is the
best eligible thread on core `c`.  A core with no current thread has no
caller: `.illegalState`. -/
def yieldOnCore (st : SystemState) (c : CoreId) : Except KernelError SystemState :=
  match st.scheduler.currentOnCore c with
  | none => .error .illegalState
  | some tid =>
    match yieldChargeOnCore st c tid with
    | .error e => .error e
    | .ok st' => scheduleEffectiveOnCore st' c

-- ─ SM5.D.6 (separate per-core domain-boundary re-dispatch, faithful to the
--   single-core `switchDomain` / `scheduleDomain` split) ─

/-- WS-ZA ZA4.5: the queue a domain switch leaves on core `c`: the outgoing
current (if it resolves) inserted at its boosted priority. -/
noncomputable def requeueOutgoingQueue (st : SystemState) (c : CoreId) : RunQueue :=
  match st.scheduler.currentOnCore c with
  | none => st.scheduler.runQueueOnCore c
  | some tid =>
      match st.getTcb? tid with
      | some tcb =>
          if st.runEnqueueAdmits c tid then
            (st.scheduler.runQueueOnCore c).insert tid tcb.boostedPriority
          else st.scheduler.runQueueOnCore c
      | none => st.scheduler.runQueueOnCore c

/-- WS-ZA ZA4.5: the domain switch's save and re-enqueue.  Core `c`'s outgoing
current has its registers saved and goes back on core `c`'s queue through its
TCB run-queue links.  Admission (`runEnqueueAdmits`) is read before the save,
which writes only the register file and so cannot change it; a current thread
queued on another core is left where it is, as `runEnqueueOnCore` leaves it. -/
def requeueOutgoingOnCore (st : SystemState) (c : CoreId) : SystemState :=
  let stSaved := saveOutgoingContextOnCore st c
  match st.scheduler.currentOnCore c with
  | none => stSaved
  | some tid =>
      match st.getTcb? tid with
      | some tcb =>
          if st.runEnqueueAdmits c tid then
            stSaved.runEnqueueAdmitted c tid tcb.boostedPriority
          else stSaved
      | none => stSaved

/-- The re-enqueue touches the object store only in run-queue links past the
context save. -/
theorem requeueOutgoingOnCore_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId) :
    (requeueOutgoingOnCore st c).objectsAgreeOffRunLinks (saveOutgoingContextOnCore st c) := by
  unfold requeueOutgoingOnCore; dsimp only
  split
  · exact .refl _
  · split
    · split
      · exact SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ _ _ _
      · exact .refl _
    · exact .refl _

/-- The re-enqueue leaves the machine where the context save left it. -/
@[simp] theorem requeueOutgoingOnCore_machine (st : SystemState) (c : CoreId) :
    (requeueOutgoingOnCore st c).machine = (saveOutgoingContextOnCore st c).machine := by
  unfold requeueOutgoingOnCore; dsimp only
  split
  · rfl
  · split
    · split
      · exact SystemState.runEnqueueAdmitted_machine _ _ _ _
      · rfl
    · rfl

/-- The re-enqueue's scheduler: core `c`'s queue is `requeueOutgoingQueue` and
its ends are rewritten; every other slot is the pre-state's. -/
theorem requeueOutgoingOnCore_scheduler (st : SystemState) (c : CoreId) :
    ∃ E, (requeueOutgoingOnCore st c).scheduler =
      (st.scheduler.setRunQueueEndsOnCore c E).setRunQueueOnCore c (requeueOutgoingQueue st c) := by
  unfold requeueOutgoingOnCore requeueOutgoingQueue; dsimp only
  split
  · refine ⟨st.scheduler.runQueueEndsOnCore c, ?_⟩
    simp [SchedulerState.setRunQueueOnCore_runQueueOnCore]
  · split
    · split
      · exact ⟨_, by simp [SystemState.runEnqueueAdmitted_scheduler]; rfl⟩
      · refine ⟨st.scheduler.runQueueEndsOnCore c, ?_⟩
        simp [SchedulerState.setRunQueueOnCore_runQueueOnCore]
    · refine ⟨st.scheduler.runQueueEndsOnCore c, ?_⟩
      simp [SchedulerState.setRunQueueOnCore_runQueueOnCore]

/-- WS-SM SM5.D.6 (per-core domain switch): the per-core analogue of
`switchDomain`.  Advances core `c` to the next domain-schedule entry, saving the
outgoing thread's register context, re-enqueueing core `c`'s current thread at
`TCB.boostedPriority`, clearing `currentOnCore c`, and writing core `c`'s
active-domain / time-remaining / schedule-index slots.

Reads / writes only core `c`'s slots (plus the object store via the context
save).  Single-domain mode (`domainSchedule = []`) is a no-op; the unreachable
out-of-bounds index surfaces `.schedulerInvariantViolation` (AK2-I, mirroring
`switchDomain`).  This is the full domain-boundary re-dispatch counterpart of
`decrementDomainTimeOnCore` (which is the lightweight in-tick accounting). -/
def switchDomainOnCore (st : SystemState) (c : CoreId) :
    Except KernelError SystemState :=
  match st.scheduler.domainSchedule with
  | [] => .ok st  -- single-domain mode: no-op
  | _ =>
      let nextIdx := ((st.scheduler.domainScheduleIndexOnCore c) + 1) % st.scheduler.domainSchedule.length
      match st.scheduler.domainSchedule[nextIdx]? with
      | none => .error .schedulerInvariantViolation
      | some entry =>
          let stQueued := requeueOutgoingOnCore st c
          let sched' := (((stQueued.scheduler.setCurrentOnCore
              c none).setActiveDomainOnCore c (DomainScheduleEntry.domain entry)).setDomainTimeRemainingOnCore
              c (DomainScheduleEntry.length entry)).setDomainScheduleIndexOnCore c nextIdx
          .ok { stQueued with scheduler := sched' }

/-- WS-SM SM5.D.6 (per-core domain tick): the per-core analogue of
`scheduleDomain`.  With a **non-empty** domain schedule: decrements core `c`'s
domain time remaining; on expiry, performs the per-core domain switch
(`switchDomainOnCore` — save the outgoing current, re-enqueue it at
`TCB.boostedPriority`, rotate to the next entry, reload the domain
quantum) and re-dispatches via the budget-aware `scheduleEffectiveOnCore` (so a
domain boundary never dispatches a budget-exhausted thread — a deliberate
budget-aware refinement over the single-core `scheduleDomain`, which uses the
non-budget `schedule`).

**Single-domain mode (`domainSchedule = []`, the RPi5 v1.0.0 default) is
inert (PR #880 review rounds 2 + 4).**  An empty schedule has no domains to
account: no boundary exists, so nothing decrements, rotates or re-dispatches
here — this transition is the identity.  Round 2 made the then-live
empty-schedule boundary re-enqueue its outgoing current (closing the
drop-current hazard); round 4 surfaced the deeper artifact that arm
inherited: with no schedule entry to reload the quantum from,
`domainTimeRemainingOnCore` stayed at the boundary forever once reached, so
*every* subsequent tick re-prepped and re-dispatched — degrading the budget
tick's time-slice quantum to per-tick churn (an equal-priority switch the
budget tick had just made could be immediately reversed).  The honest
semantics for "no domain schedule" is **no domain scheduling**: time-slice
fairness belongs to the budget tick (`timerTickBudgetOnCore` preempts on
slice expiry and re-dispatches budget-aware), idle adoption on the live
paths belongs to the wake receiver (`handleRescheduleSgiOnCore`), the
vacate-successor seam and the budget tick's own re-dispatch fallback, and
the domain layer provably cannot perturb any of them
(`scheduleDomainOnCore_singleDomain_inert`).  Domain accounting — the
decrement, the boundary rotation + re-dispatch, and the idle-adoption
witness `scheduleDomainOnCore_runs_idle` — is the non-empty arm's, exactly
as in seL4, whose domain schedule always carries at least one entry. -/
def scheduleDomainOnCore (st : SystemState) (c : CoreId) :
    Except KernelError SystemState :=
  match st.scheduler.domainSchedule with
  | [] => .ok st  -- single-domain mode: no domains to account (inert)
  | _ :: _ =>
      if (st.scheduler.domainTimeRemainingOnCore c) ≤ 1 then
        match switchDomainOnCore st c with
        | .error e => .error e
        | .ok st' => scheduleEffectiveOnCore st' c
      else
        -- non-boundary: decrement core `c`'s domain time (`> 1`, so stays `≥ 1`).
        .ok (decrementDomainTimeOnCore st c)

/-- WS-SM SM5.D.6 (PR #880 round 4): in single-domain mode the domain tick is
the identity — the headline witness that on the RPi5 v1.0.0 default
configuration the domain layer cannot perturb scheduling (no spurious
boundary, no per-tick re-dispatch, no quantum interference with the budget
tick's time-slice accounting). -/
theorem scheduleDomainOnCore_singleDomain_inert (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule = []) :
    scheduleDomainOnCore st c = .ok st := by
  unfold scheduleDomainOnCore
  rw [hSched]

-- The domain accounting never refuses (WS-ZA ZA6.1).

/-- `switchDomainOnCore`'s state, which it always reaches
(`switchDomainOnCore_eq_state`): the next index is taken modulo the schedule's
length, so the entry it names exists. -/
@[inline] def switchDomainOnCoreState (st : SystemState) (c : CoreId) : SystemState :=
  match st.scheduler.domainSchedule with
  | [] => st
  | _ =>
      let nextIdx := ((st.scheduler.domainScheduleIndexOnCore c) + 1) % st.scheduler.domainSchedule.length
      match st.scheduler.domainSchedule[nextIdx]? with
      | none => st
      | some entry =>
          let stQueued := requeueOutgoingOnCore st c
          let sched' := (((stQueued.scheduler.setCurrentOnCore
              c none).setActiveDomainOnCore c (DomainScheduleEntry.domain entry)).setDomainTimeRemainingOnCore
              c (DomainScheduleEntry.length entry)).setDomainScheduleIndexOnCore c nextIdx
          { stQueued with scheduler := sched' }

theorem switchDomainOnCore_eq_state (st : SystemState) (c : CoreId) :
    switchDomainOnCore st c = .ok (switchDomainOnCoreState st c) := by
  unfold switchDomainOnCore switchDomainOnCoreState
  cases hS : st.scheduler.domainSchedule with
  | nil => rfl
  | cons e rest =>
    simp only
    have hLt : ((st.scheduler.domainScheduleIndexOnCore c) + 1) % (e :: rest).length
        < (e :: rest).length := Nat.mod_lt _ (by simp)
    rw [List.getElem?_eq_getElem hLt]

/-- `scheduleDomainOnCore`'s state, which it always reaches
(`scheduleDomainOnCore_eq_state`). -/
@[inline] def scheduleDomainOnCoreState (st : SystemState) (c : CoreId) : SystemState :=
  match st.scheduler.domainSchedule with
  | [] => st
  | _ :: _ =>
      if (st.scheduler.domainTimeRemainingOnCore c) ≤ 1 then
        scheduleEffectiveOnCoreState (switchDomainOnCoreState st c) c
      else decrementDomainTimeOnCore st c

theorem scheduleDomainOnCore_eq_state (st : SystemState) (c : CoreId) :
    scheduleDomainOnCore st c = .ok (scheduleDomainOnCoreState st c) := by
  unfold scheduleDomainOnCore scheduleDomainOnCoreState
  cases st.scheduler.domainSchedule with
  | nil => rfl
  | cons e rest =>
    simp only
    split
    · rw [switchDomainOnCore_eq_state]; exact scheduleEffectiveOnCore_eq_state _ _
    · rfl


-- ============================================================================
-- V8-G3: ThreadState synchronization
-- ============================================================================

/-- **WS-SM SM4.C.11 / WS-RR RR5.10**: is `tid` the current thread of **some**
core?

The per-core lift of the `currentOnCore bootCoreId` test `inferThreadState` used
to make.  A thread runs on exactly one core, but the classification has to look
at every core to find out which — asking the boot core alone answers "no" for a
thread running on a secondary, which is a different claim.

Decidable by construction: `allCores` is `List.finRange numCores`, so the
existential is a fold over a finite list rather than a quantifier.

**WS-RR RR7.36 — this is `Selection.runningOnSomeCore`, not a second answer to
its question.**  SM5.D.4 had already asked "is `tid` current on some core?" for
the cross-core replenish wake, whose whole job is to keep one TCB from being
dispatchable on two cores; RR5.10 asked it again here, in a module that does not
import that one, and wrote a second fold over `allCores`.  Two implementations of
one question diverge (`CLAUDE.md`, *one question answered in two places*), and
this pair diverging is not a cosmetic defect: the wake's single-placement guard
and the thread-state classification would disagree about whether a thread is
placed, so a thread could be enqueued a second time while still classifying as
running.  So the classification is *defined as* the guard's predicate rather than
stated to equal it — the divergence is impossible instead of merely checked. -/
def threadRunningOnSomeCore (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  runningOnSomeCore st tid

/-- **WS-SM SM4.C.11 / WS-RR RR5.10**: is `tid` in **some** core's run queue?
The per-core lift of the `runQueueOnCore bootCoreId` test (see
`threadRunningOnSomeCore`).

**WS-RR RR7.36**: likewise `Selection.runnableOnSomeCore` — SM5.C.1's
single-placement test — rather than a second fold spelling run-queue membership
`decide (tid ∈ ·)` where that one spells it `RunQueue.contains`.  The two
spellings agree (`Membership` on `RunQueue` *is* `contains … = true`), which is
exactly what makes a divergence between them silent. -/
def threadQueuedOnSomeCore (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  runnableOnSomeCore st tid

/-- **WS-RR RR7.36**: the classification's running test and the cross-core wake's
single-placement test are the same function.  Definitional, and stated so a
reader of either module finds the other. -/
theorem threadRunningOnSomeCore_eq_runningOnSomeCore
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    threadRunningOnSomeCore st tid = runningOnSomeCore st tid := rfl

/-- **WS-RR RR7.36**: the run-queue half of the same identification. -/
theorem threadQueuedOnSomeCore_eq_runnableOnSomeCore
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    threadQueuedOnSomeCore st tid = runnableOnSomeCore st tid := rfl

/-- V8-G3: Infer the `ThreadState` for a thread based on observable system state.
This is the canonical definition of what each `ThreadState` value means:
- `Running`: thread is the current thread of some core
- `Ready`: thread is in some core's run queue, or is an idle thread its core is
  not running: an idle thread is never queued (seL4 never enqueues it) and is
  always ready, the thread its core falls back to when its queue is empty
- `BlockedSend`/`BlockedRecv`/`BlockedCall`/`BlockedReply`/`BlockedNotif`: matches `ipcState`
- `Inactive`: none of the above (ipcState.ready but not queued/current)

**WS-RR RR5.10 — the classification is no longer boot-core-pinned.**  The two
tests above read `currentOnCore bootCoreId` / `runQueueOnCore bootCoreId`, so a
thread running on a secondary core classified `.Inactive`: its own core's current
slot pointed at it, but no boot-core slot did.  That is register §7 finding 42,
and it stops being latent the moment the boot path installs per-core idle
threads — the boot state stores each core's idle thread as `readyIdleThread`
(`.Ready`; before the PR #889 review round it stored the dispatched
`createIdleThread` form, `.Running`), so a classification that missed it would
re-infer core 1's idle TCB `.Inactive`, `threadStateConsistent` would be false of
the boot state, and `assertStateInvariantsFor` (which syncs before it checks)
would *rewrite the field* rather than report the mismatch.  RR5.13/RR5.14 make
that boot state the production one, which is why this lift lands first.

The lift is conservative on any state the old definition classified: with
`currentOnCore c = none` and an empty `runQueueOnCore c` on every secondary — the
shape of every pre-RR5.14 boot state — `threadRunningOnSomeCore` and
`threadQueuedOnSomeCore` agree with the boot-core tests
(`inferThreadState_eq_bootCore_of_secondaries_quiescent`). -/
def inferThreadState (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) : ThreadState :=
  if threadRunningOnSomeCore st tid then .Running
  else if threadQueuedOnSomeCore st tid then .Ready
  else if isIdleThreadId tid then .Ready
  else match tcb.ipcState with
  | .blockedOnSend _ => .BlockedSend
  | .blockedOnReceive _ => .BlockedRecv
  | .blockedOnCall _ => .BlockedCall
  | .blockedOnNotification _ => .BlockedNotif
  | .blockedOnReply _ _ => .BlockedReply
  | .ready => .Inactive

/-- V8-G3: Synchronize all TCB `threadState` fields to match observable state.
Idempotent: calling this twice produces the same result.
This function is called after kernel operations to maintain the `threadState`
field without modifying the operations themselves (preserving all existing proofs). -/
def syncThreadStates (st : SystemState) : SystemState :=
  let objs := st.objects.fold (init := st.objects) fun acc oid obj =>
    match obj with
    | .tcb tcb =>
      let expected := inferThreadState st ⟨oid.toNat⟩ tcb
      if tcb.threadState == expected then acc
      else acc.insert oid (.tcb { tcb with threadState := expected })
    | _ => acc
  { st with objects := objs }

/-- V8-G2: ThreadState consistency predicate — the `threadState` field of every
TCB matches the state inferred from queue membership and IPC state.

**WS-RR RR5.10**: inherits the per-core lift from `inferThreadState`, so a thread
running on a secondary core satisfies this rather than falsifying it. -/
def threadStateConsistent (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (tcb : TCB),
    st.objects[oid]? = some (.tcb tcb) →
    tcb.threadState = inferThreadState st ⟨oid.toNat⟩ tcb

/-- PR #889 review round 2: the relation the **live** kernel actually keeps on
the stored `threadState` field, stated on its own so it can be cited honestly.

`threadStateConsistent` is the full classification and holds of the production
boot state (`bootFromPlatformCheckedWithIdleThreads_threadStateConsistent`); it
is **not** preserved by the transitions, because no scheduler dispatch writes
`.Running` and no IPC block writes a `.Blocked*` — `scheduleEffectiveOnCore` /
`switchToThreadOnCore` move the current slot and the run queue and leave the
TCB object alone, so after any core's first dispatch the field says `.Ready` of
a running thread, and after any rendezvous it says `.Ready` of a blocked one.
The harness re-establishes the full classification with `syncThreadStates`
before it checks.

What the live decisions read is narrower: `tcbSuspend` / `tcbResume` / the
cross-core cancellation / the fault suspend test the field against `.Inactive`
only (`Lifecycle/Suspend.lean`, `IPC/CrossCore/Cancellation.lean`), and the
writers of the field are exactly the lifecycle transitions that make a thread
inactive or ready again.  This predicate is that reading: the stored flag says
`.Inactive` **iff** the observable state classifies the thread `.Inactive`.
It follows from the full classification (`threadStateConsistent_implies_
threadInactiveFlagConsistent`), so it holds of the boot state too; its
preservation across the scheduler and IPC surfaces — or the replacement of the
stored field by the inferred one — is registered debt
(`docs/REGISTERED_DEBT.md`, owned by WS-RR RR7.36), not a theorem of this cut.
New code must not cite `threadStateConsistent` of a post-dispatch state. -/
def threadInactiveFlagConsistent (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (tcb : TCB),
    st.objects[oid]? = some (.tcb tcb) →
    (tcb.threadState = .Inactive ↔ inferThreadState st ⟨oid.toNat⟩ tcb = .Inactive)

/-- PR #889 review round 2: the full classification entails the inactive-flag
relation — what carries the boot-state result over. -/
theorem threadStateConsistent_implies_threadInactiveFlagConsistent
    (st : SystemState) (h : threadStateConsistent st) :
    threadInactiveFlagConsistent st := by
  intro oid tcb hObj
  rw [h oid tcb hObj]

/-- **WS-RR RR5.10**: a thread that is some core's current thread classifies
`.Running` — for **every** core, not only the boot core.  The substantive
content of the lift: this is false of the pre-RR5.10 definition whenever `c` is
a secondary. -/
theorem inferThreadState_running_of_currentOnCore (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : st.scheduler.currentOnCore c = some tid) :
    inferThreadState st tid tcb = .Running := by
  have hRun : threadRunningOnSomeCore st tid = true := by
    simp only [threadRunningOnSomeCore, runningOnSomeCore, List.any_eq_true]
    exact ⟨c, SeLe4n.Kernel.Concurrency.mem_allCores c, by simp [h]⟩
  simp only [inferThreadState, hRun, if_true]

/-- **WS-RR RR5.10**: a thread in some core's run queue that is nobody's current
thread classifies `.Ready` — again for every core. -/
theorem inferThreadState_ready_of_runQueueOnCore (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hQueued : st.queuedOn c tid = true)
    (hNotCurrent : threadRunningOnSomeCore st tid = false) :
    inferThreadState st tid tcb = .Ready := by
  have hQ : threadQueuedOnSomeCore st tid = true := by
    simp only [threadQueuedOnSomeCore, runnableOnSomeCore, List.any_eq_true]
    exact ⟨c, SeLe4n.Kernel.Concurrency.mem_allCores c, hQueued⟩
  simp only [inferThreadState, hNotCurrent, hQ, Bool.false_eq_true, if_false, if_true]

/-- **WS-RR RR5.10** (conservativity): on a state whose secondary cores are
quiescent — no current thread and an empty run queue on every core but the boot
core — the lifted classification is exactly the boot-core-pinned one it replaced.

This is what makes the lift safe for every state the tree already reasons about:
the pre-RR5.14 boot path leaves `currentOnCore c = none` on every core
(`bootFromPlatform_smp_currentAllNone`), and the single-core fixtures the suites
build populate the boot core only.  The theorem is stated over the two tests
rather than over `inferThreadState` itself so it composes with either branch. -/
theorem threadRunningOnSomeCore_eq_bootCore_of_secondaries_quiescent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hQuiet : ∀ c : SeLe4n.Kernel.Concurrency.CoreId, c ≠ bootCoreId →
      st.scheduler.currentOnCore c = none) :
    threadRunningOnSomeCore st tid =
      ((st.scheduler.currentOnCore bootCoreId) == some tid) := by
  simp only [threadRunningOnSomeCore, runningOnSomeCore]
  cases hBoot : (st.scheduler.currentOnCore bootCoreId) == some tid with
  | true =>
      simp only [List.any_eq_true]
      exact ⟨bootCoreId, SeLe4n.Kernel.Concurrency.mem_allCores bootCoreId, hBoot⟩
  | false =>
      simp only [List.any_eq_false]
      intro c _
      by_cases hc : c = bootCoreId
      · subst hc; simp [hBoot]
      · simp [hQuiet c hc]

/-- **WS-RR RR5.10** (conservativity, the run-queue half). -/
theorem threadQueuedOnSomeCore_eq_bootCore_of_secondaries_quiescent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hQuiet : ∀ c : SeLe4n.Kernel.Concurrency.CoreId, c ≠ bootCoreId →
      st.queuedOn c tid = false) :
    threadQueuedOnSomeCore st tid = st.queuedOn bootCoreId tid := by
  simp only [threadQueuedOnSomeCore, runnableOnSomeCore]
  cases hBoot : st.queuedOn bootCoreId tid with
  | true =>
      simp only [List.any_eq_true]
      exact ⟨bootCoreId, SeLe4n.Kernel.Concurrency.mem_allCores bootCoreId, hBoot⟩
  | false =>
      simp only [List.any_eq_false]
      intro c _
      by_cases hc : c = bootCoreId
      · subst hc; simp [hBoot]
      · simp [hQuiet c hc]

/-- **WS-RR RR5.10** (conservativity, composed): on a quiescent-secondary state
the lifted `inferThreadState` returns exactly what the boot-core-pinned
definition returned. -/
theorem inferThreadState_eq_bootCore_of_secondaries_quiescent
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hCurrent : ∀ c : SeLe4n.Kernel.Concurrency.CoreId, c ≠ bootCoreId →
      st.scheduler.currentOnCore c = none)
    (hQueue : ∀ c : SeLe4n.Kernel.Concurrency.CoreId, c ≠ bootCoreId →
      st.queuedOn c tid = false) :
    inferThreadState st tid tcb =
      (if (st.scheduler.currentOnCore bootCoreId) == some tid then .Running
       else if st.queuedOn bootCoreId tid then .Ready
       else if isIdleThreadId tid then .Ready
       else match tcb.ipcState with
         | .blockedOnSend _ => .BlockedSend
         | .blockedOnReceive _ => .BlockedRecv
         | .blockedOnCall _ => .BlockedCall
         | .blockedOnNotification _ => .BlockedNotif
         | .blockedOnReply _ _ => .BlockedReply
         | .ready => .Inactive) := by
  simp only [inferThreadState,
    threadRunningOnSomeCore_eq_bootCore_of_secondaries_quiescent st tid hCurrent,
    threadQueuedOnSomeCore_eq_bootCore_of_secondaries_quiescent st tid hQueue]


-- ============================================================================
-- WS-RR RR7.36 — preservation of the inactive-flag relation
--
-- `threadStateConsistent` is a boot-state theorem and false after any core's
-- first dispatch; `threadInactiveFlagConsistent` is the relation the *live*
-- decisions read (`tcbSuspend` / `tcbResume` / the cross-core cancellation /
-- the fault suspend all test the field against `.Inactive` only), and its
-- preservation is what `docs/REGISTERED_DEBT.md` records as owed.  This section
-- discharges it for the per-core context switch and the primitives it composes,
-- and states the frame the remaining surfaces will use.
--
-- The two side conditions on the dispatch are the two ways the relation
-- genuinely breaks, not proof bookkeeping: placing a thread the state
-- classifies `.Inactive`, and stranding a displaced thread off every queue.
-- ============================================================================

def threadPlacedOnSomeCore (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  threadRunningOnSomeCore st tid || threadQueuedOnSomeCore st tid

theorem inferThreadState_eq_inactive_iff (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) :
    inferThreadState st tid tcb = .Inactive ↔
      (threadPlacedOnSomeCore st tid = false ∧ isIdleThreadId tid = false ∧
        tcb.ipcState = .ready) := by
  unfold inferThreadState threadPlacedOnSomeCore
  cases hRun : threadRunningOnSomeCore st tid <;>
    cases hQ : threadQueuedOnSomeCore st tid <;>
      cases hI : isIdleThreadId tid <;>
        cases hIpc : tcb.ipcState <;> simp


theorem threadInactiveFlagConsistent_of_frame (st st' : SystemState)
    (hTcb : ∀ (oid : SeLe4n.ObjId) (tcb' : TCB), st'.objects[oid]? = some (.tcb tcb') →
      ∃ tcb, st.objects[oid]? = some (.tcb tcb) ∧
        tcb'.threadState = tcb.threadState ∧ tcb'.ipcState = tcb.ipcState)
    (hPlaced : ∀ tid, threadPlacedOnSomeCore st' tid = threadPlacedOnSomeCore st tid)
    (h : threadInactiveFlagConsistent st) :
    threadInactiveFlagConsistent st' := by
  intro oid tcb' hObj
  obtain ⟨tcb, hPre, hState, hIpc⟩ := hTcb oid tcb' hObj
  have hOld := h oid tcb hPre
  rw [hState, inferThreadState_eq_inactive_iff, hIpc, hPlaced,
    ← inferThreadState_eq_inactive_iff]
  exact hOld

theorem threadInactiveFlagConsistent_of_frame_placing (st st' : SystemState)
    (moved : SeLe4n.ThreadId)
    (hTcb : ∀ (oid : SeLe4n.ObjId) (tcb' : TCB), st'.objects[oid]? = some (.tcb tcb') →
      ∃ tcb, st.objects[oid]? = some (.tcb tcb) ∧
        tcb'.threadState = tcb.threadState ∧ tcb'.ipcState = tcb.ipcState)
    (hOthers : ∀ tid, tid ≠ moved → isIdleThreadId tid = false →
      threadPlacedOnSomeCore st' tid = threadPlacedOnSomeCore st tid)
    (hMovedNow : threadPlacedOnSomeCore st' moved = true)
    (hMovedActive : ∀ tcb, st.getTcb? moved = some tcb →
      inferThreadState st moved tcb ≠ .Inactive)
    (h : threadInactiveFlagConsistent st) :
    threadInactiveFlagConsistent st' := by
  intro oid tcb' hObj
  obtain ⟨tcb, hPre, hState, hIpc⟩ := hTcb oid tcb' hObj
  by_cases hEq : (⟨oid.toNat⟩ : SeLe4n.ThreadId) = moved
  · subst hEq
    have hNot := hMovedActive tcb ((SystemState.getTcb?_eq_some_iff st _ tcb).mpr hPre)
    constructor
    · intro hFlag
      exact absurd (by
        rw [hState] at hFlag
        exact ((h oid tcb hPre).mp hFlag)) hNot
    · intro hInf
      rw [inferThreadState_eq_inactive_iff, hMovedNow] at hInf
      exact absurd hInf.1 (by simp)
  · have hOld := h oid tcb hPre
    rw [inferThreadState_eq_inactive_iff] at hOld
    rw [hState, inferThreadState_eq_inactive_iff, hIpc]
    cases hI : isIdleThreadId ⟨oid.toNat⟩
    · rw [hOthers _ hEq hI]; rw [hI] at hOld; exact hOld
    · simpa [hI] using hOld


/-- **WS-RR RR8.12 (Cut 4)**: placement is a question about `u`'s **own** slots,
so a step frames it by agreeing *at `u`* — not by leaving the slots equal.

`threadPlacedOnSomeCore_congr` below asks for the `current` slots to be equal,
which a deschedule of a **different** thread falsifies: the slot that held the
descheduled thread becomes `none`.  The suspend pipeline's G4 is exactly that
step, so the equality form cannot frame it and this one can.  The equality form
is now this one's instance rather than a second reading of the same question. -/
theorem threadPlacedOnSomeCore_congr_at (st st' : SystemState) (u : SeLe4n.ThreadId)
    (hCur : ∀ c : CoreId,
      st'.scheduler.currentOnCore c = some u ↔ st.scheduler.currentOnCore c = some u)
    (hQ : ∀ c : CoreId, st'.queuedOn c u = st.queuedOn c u) :
    threadPlacedOnSomeCore st' u = threadPlacedOnSomeCore st u := by
  have hRunFn : (fun c : CoreId => (st'.scheduler.currentOnCore c) == some u)
      = (fun c : CoreId => (st.scheduler.currentOnCore c) == some u) := by
    funext c
    exact Bool.eq_iff_iff.mpr (by simpa using hCur c)
  have hQFn : (fun c : CoreId => st'.queuedOn c u)
      = (fun c : CoreId => st.queuedOn c u) := funext hQ
  unfold threadPlacedOnSomeCore threadRunningOnSomeCore threadQueuedOnSomeCore
    runningOnSomeCore runnableOnSomeCore
  rw [hRunFn, hQFn]

/-- Placement is read off the two per-core slot families, so pointwise equality
of both families gives it — the instance of `threadPlacedOnSomeCore_congr_at`
where the `current` slots agree outright. -/
theorem threadPlacedOnSomeCore_congr (st st' : SystemState) (u : SeLe4n.ThreadId)
    (hCur : ∀ c : CoreId, st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hQ : ∀ c : CoreId, st'.queuedOn c u = st.queuedOn c u) :
    threadPlacedOnSomeCore st' u = threadPlacedOnSomeCore st u :=
  threadPlacedOnSomeCore_congr_at st st' u (fun c => by rw [hCur c]) hQ


theorem threadRunningOnSomeCore_of_currentOnCore (st : SystemState) (c : CoreId)
    (u : SeLe4n.ThreadId) (h : st.scheduler.currentOnCore c = some u) :
    threadRunningOnSomeCore st u = true := by
  simp only [threadRunningOnSomeCore, runningOnSomeCore, List.any_eq_true]
  exact ⟨c, SeLe4n.Kernel.Concurrency.mem_allCores c, by simp [h]⟩

/-- **WS-RR RR7.36**: overwriting one TCB with a record that agrees on the two
fields this relation reads frames every stored TCB's reading of them. -/
theorem objects_insert_tcb_frame (st : SystemState) (k : SeLe4n.ObjId)
    (saved prev : TCB) (hObjInv : st.objects.invExt)
    (hPrev : st.objects[k]? = some (.tcb prev))
    (hState : saved.threadState = prev.threadState)
    (hIpc : saved.ipcState = prev.ipcState)
    (oid : SeLe4n.ObjId) (tcb' : TCB)
    (hObj : (st.objects.insert k (.tcb saved))[oid]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[oid]? = some (.tcb tcb) ∧
      tcb'.threadState = tcb.threadState ∧ tcb'.ipcState = tcb.ipcState := by
  have hObj' : (st.objects.insert k (.tcb saved)).get? oid = some (.tcb tcb') := hObj
  by_cases hOid : oid = k
  · subst hOid
    rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv] at hObj'
    cases hObj'
    exact ⟨prev, hPrev, hState, hIpc⟩
  · rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _
      (fun hEq => hOid (eq_of_beq hEq).symm) hObjInv] at hObj'
    exact ⟨tcb', hObj', rfl, rfl⟩

/-- **WS-RR RR7.36**: saving the outgoing thread's registers and re-enqueueing it
on the core it was running on leaves every thread's *placement* unchanged.  The
outgoing thread swaps running for queued — both are placed — and no other
thread's slot moves. -/
theorem threadPlacedOnSomeCore_save_and_reenqueue
    (st : SystemState) (c : CoreId) (prevTid u : SeLe4n.ThreadId)
    (saved : KernelObject) (prio : SeLe4n.Priority) (hObjInv : st.objects.invExt)
    (hCur : st.scheduler.currentOnCore c = some prevTid) :
    threadPlacedOnSomeCore
      (({ st with objects := st.objects.insert prevTid.toObjId saved } : SystemState
        ).runEnqueueOnCore c prevTid prio) u
      = threadPlacedOnSomeCore st u := by
  by_cases hu : u = prevTid
  · subst hu
    have hRun : threadRunningOnSomeCore st u = true :=
      threadRunningOnSomeCore_of_currentOnCore st c u hCur
    have hRun' : threadRunningOnSomeCore
        (({ st with objects := st.objects.insert u.toObjId saved } : SystemState
          ).runEnqueueOnCore c u prio) u = true :=
      threadRunningOnSomeCore_of_currentOnCore _ c u (by
        rw [SystemState.runEnqueueOnCore_currentOnCore]; exact hCur)
    simp [threadPlacedOnSomeCore, hRun, hRun']
  · refine threadPlacedOnSomeCore_congr st _ u
      (fun c' => SystemState.runEnqueueOnCore_currentOnCore _ _ _ _ _) (fun c' => ?_)
    rw [SystemState.runEnqueueOnCore_queuedOn, if_neg (fun h => hu h.1)]
    apply SystemState.queuedOn_of_getTcb?
    have hNe : ¬ (prevTid.toObjId == u.toObjId) = true :=
      fun hh => hu (SeLe4n.ThreadId.toObjId_injective _ _ (eq_of_beq hh)).symm
    simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
    rw [RobinHood.RHTable.getElem?_insert_ne st.objects prevTid.toObjId u.toObjId _ hNe hObjInv]

/-- The shape a context-switch preempt leaves: the outgoing thread's TCB is
rewritten with a new register context only, and it is re-enqueued on the core it
was running on.  Stated over the shape rather than over `preemptCurrentOnCore`
so the two consumers below share one argument. -/
theorem threadInactiveFlagConsistent_save_and_reenqueue
    (st : SystemState) (c : CoreId) (prevTid : SeLe4n.ThreadId)
    (prevTcb saved : TCB) (prio : SeLe4n.Priority)
    (hObjInv : st.objects.invExt)
    (hPrevObj : st.getTcb? prevTid = some prevTcb)
    (hCur : st.scheduler.currentOnCore c = some prevTid)
    (hState : saved.threadState = prevTcb.threadState)
    (hIpc : saved.ipcState = prevTcb.ipcState)
    (h : threadInactiveFlagConsistent st) :
    threadInactiveFlagConsistent
      (({ st with objects := st.objects.insert prevTid.toObjId (.tcb saved) } : SystemState
        ).runEnqueueOnCore c prevTid prio) := by
  refine threadInactiveFlagConsistent_of_frame st _ ?_ ?_ h
  · intro oid tcb' hObj
    obtain ⟨t0, h0, hE⟩ :=
      (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ c prevTid prio).get_tcb' hObj
    obtain ⟨tcb, hT, hS, hI⟩ := objects_insert_tcb_frame st prevTid.toObjId saved prevTcb
      hObjInv ((SystemState.getTcb?_eq_some_iff st prevTid prevTcb).mp hPrevObj)
      hState hIpc oid t0 h0
    exact ⟨tcb, hT, (TCB.proj_eq_of_withoutRunLinks_eq TCB.threadState hE).trans hS,
      (TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hE).trans hI⟩
  · intro u
    exact threadPlacedOnSomeCore_save_and_reenqueue st c prevTid u _ prio hObjInv hCur

theorem preemptCurrentOnCore_preserves_threadInactiveFlagConsistent
    (st : SystemState) (c : CoreId) (incoming : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : threadInactiveFlagConsistent st) :
    threadInactiveFlagConsistent (preemptCurrentOnCore st c incoming) := by
  unfold preemptCurrentOnCore
  split
  · exact h
  · rename_i prevTid hCur
    split
    · exact h
    · split
      · rename_i prevTcb hPrev hW
        exact threadInactiveFlagConsistent_save_and_reenqueue st c prevTid prevTcb _ _
          hObjInv hPrev hCur rfl rfl h
      · exact h


theorem threadPlacedOnSomeCore_eq_true_iff (st : SystemState) (u : SeLe4n.ThreadId) :
    threadPlacedOnSomeCore st u = true ↔
      ((∃ c : CoreId, st.scheduler.currentOnCore c = some u) ∨
       (∃ c : CoreId, st.queuedOn c u = true)) := by
  unfold threadPlacedOnSomeCore threadRunningOnSomeCore threadQueuedOnSomeCore
    runningOnSomeCore runnableOnSomeCore
  simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro (⟨c, _, hc⟩ | ⟨c, _, hc⟩)
    · exact Or.inl ⟨c, hc⟩
    · exact Or.inr ⟨c, hc⟩
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · exact Or.inl ⟨c, SeLe4n.Kernel.Concurrency.mem_allCores c, hc⟩
    · exact Or.inr ⟨c, SeLe4n.Kernel.Concurrency.mem_allCores c, hc⟩

theorem threadQueuedOnSomeCore_eq_true_iff (st : SystemState) (u : SeLe4n.ThreadId) :
    threadQueuedOnSomeCore st u = true ↔ ∃ c : CoreId, st.queuedOn c u = true := by
  unfold threadQueuedOnSomeCore runnableOnSomeCore
  simp only [List.any_eq_true]
  exact ⟨fun ⟨c, _, hc⟩ => ⟨c, hc⟩,
    fun ⟨c, hc⟩ => ⟨c, SeLe4n.Kernel.Concurrency.mem_allCores c, hc⟩⟩


/-- Placement reads the `current` slots and each thread's run-queue core, so a
step that keeps the scheduler and moves no thread on or off a run queue frames
it. -/
theorem threadPlacedOnSomeCore_of_scheduler_eq (st st' : SystemState)
    (u : SeLe4n.ThreadId) (h : st'.scheduler = st.scheduler)
    (hQ : SystemState.RunCoresAgree st' st) :
    threadPlacedOnSomeCore st' u = threadPlacedOnSomeCore st u :=
  threadPlacedOnSomeCore_congr st st' u (fun c => by rw [h]) (fun c => hQ.queuedOn c u)

/-- **WS-RR RR8.12 (Cut 4)**: the typed in-place TCB write is one such step —
the shape the suspend pipeline's pending-state clear and `.Inactive` write both
take. -/
theorem threadPlacedOnSomeCore_updateTcb (st : SystemState) (tid u : SeLe4n.ThreadId)
    (f : TCB → TCB) (hf : ∀ x, (f x).runCoreCode = x.runCoreCode)
    (hInv : st.objects.invExt) :
    threadPlacedOnSomeCore (st.updateTcb tid f) u = threadPlacedOnSomeCore st u :=
  threadPlacedOnSomeCore_of_scheduler_eq st _ u (SystemState.updateTcb_scheduler _ _ _)
    (SystemState.updateTcb_runCoreCode st tid f hf hInv)

/-- **WS-RR RR8.12 (Cut 4)**: the dispatch step leaves every **other** thread's
placement where it was — given the one it displaces is queued somewhere.

The hypothesis is scoped to `u` rather than quantified over every thread current
on `c`, because that is what the question is about: a step that displaces a
thread other than `u` cannot unplace `u` however that thread is left.  Stated
here because `threadInactiveFlagConsistent_dispatch` below asks the same thing of
the same step and had the argument inline — one question, one answer. -/
theorem threadPlacedOnSomeCore_dispatch_ne (st : SystemState) (c : CoreId)
    (tid u : SeLe4n.ThreadId) (hu : u ≠ tid)
    (hOutgoing : st.scheduler.currentOnCore c = some u →
      threadQueuedOnSomeCore st u = true) :
    threadPlacedOnSomeCore
      { st.runRemoveOnCore c tid with scheduler :=
          (st.runRemoveOnCore c tid).scheduler.setCurrentOnCore c (some tid) } u
      = threadPlacedOnSomeCore st u := by
  have hCur' : ∀ c' : CoreId,
      ((st.runRemoveOnCore c tid).scheduler.setCurrentOnCore c (some tid)).currentOnCore c' =
      if c' = c then some tid else st.scheduler.currentOnCore c' := by
    intro c'
    by_cases hc : c' = c
    · subst hc
      rw [if_pos rfl, SchedulerState.setCurrentOnCore_currentOnCore_self]
    · rw [if_neg hc,
        SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (fun hEq => hc hEq.symm),
        SystemState.runRemoveOnCore_scheduler, SchedulerState.setRunQueueOnCore_currentOnCore,
        SchedulerState.setRunQueueEndsOnCore_currentOnCore]
  have hQ' : ∀ (c' : CoreId) (v : SeLe4n.ThreadId),
      ({ st.runRemoveOnCore c tid with scheduler :=
          (st.runRemoveOnCore c tid).scheduler.setCurrentOnCore c (some tid) } :
          SystemState).queuedOn c' v = true ↔
        (st.queuedOn c' v = true ∧ (c' = c → v ≠ tid)) := by
    intro c' v
    show (st.runRemoveOnCore c tid).queuedOn c' v = true ↔ _
    rw [SystemState.runRemoveOnCore_queuedOn]
    by_cases hv : v = tid ∧ c' = c
    · rw [if_pos hv]; exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd hv.1 (h.2 hv.2)⟩
    · rw [if_neg hv]; exact ⟨fun h => ⟨h, fun hc hvt => hv ⟨hvt, hc⟩⟩, fun h => h.1⟩
  apply Bool.eq_iff_iff.mpr
  rw [threadPlacedOnSomeCore_eq_true_iff, threadPlacedOnSomeCore_eq_true_iff]
  constructor
  · rintro (⟨c', hc'⟩ | ⟨c', hc'⟩)
    · rw [hCur' c'] at hc'
      by_cases hc : c' = c
      · subst hc; rw [if_pos rfl] at hc'; exact absurd (Option.some.inj hc').symm hu
      · rw [if_neg hc] at hc'; exact Or.inl ⟨c', hc'⟩
    · exact Or.inr ⟨c', ((hQ' c' u).mp hc').1⟩
  · rintro (⟨c', hc'⟩ | ⟨c', hc'⟩)
    · by_cases hc : c' = c
      · subst hc
        obtain ⟨c'', hc''⟩ := (threadQueuedOnSomeCore_eq_true_iff st u).mp (hOutgoing hc')
        exact Or.inr ⟨c'', (hQ' c'' u).mpr ⟨hc'', fun _ => hu⟩⟩
      · exact Or.inl ⟨c', by rw [hCur' c', if_neg hc]; exact hc'⟩
    · exact Or.inr ⟨c', (hQ' c' u).mpr ⟨hc', fun _ => hu⟩⟩

/-- **WS-RR RR8.12 (Cut 4)**: and the dispatched thread is placed, because it is
now current.  No hypothesis: the step *is* the placement. -/
theorem threadPlacedOnSomeCore_dispatch_self (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    threadPlacedOnSomeCore
      { st.runRemoveOnCore c tid with scheduler :=
          (st.runRemoveOnCore c tid).scheduler.setCurrentOnCore c (some tid) } tid
      = true := by
  rw [threadPlacedOnSomeCore_eq_true_iff]
  exact Or.inl ⟨c, SchedulerState.setCurrentOnCore_currentOnCore_self _ _ _⟩

/-- The dispatch step: dequeue `tid` from core `c` and make it current there.

The substantive side conditions are both real properties of the caller, not
bookkeeping.  `hOutgoing` says the thread this dispatch displaces is queued
somewhere, and `hActive` that the dispatched thread is not one the state
classifies `.Inactive`. -/
theorem threadInactiveFlagConsistent_dispatch (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId)
    (hOutgoing : ∀ u, u ≠ tid → isIdleThreadId u = false →
      st.scheduler.currentOnCore c = some u → threadQueuedOnSomeCore st u = true)
    (hActive : ∀ tcb, st.getTcb? tid = some tcb →
      inferThreadState st tid tcb ≠ .Inactive)
    (h : threadInactiveFlagConsistent st) :
    threadInactiveFlagConsistent
      { st.runRemoveOnCore c tid with scheduler :=
          (st.runRemoveOnCore c tid).scheduler.setCurrentOnCore c (some tid) } :=
  threadInactiveFlagConsistent_of_frame_placing st _ tid
    (fun _oid _tcb' hObj =>
      let ⟨t0, h0, hE⟩ := (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c tid).get_tcb' hObj
      ⟨t0, h0, TCB.proj_eq_of_withoutRunLinks_eq TCB.threadState hE,
        TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hE⟩)
    (fun u hu hI => threadPlacedOnSomeCore_dispatch_ne st c tid u hu (hOutgoing u hu hI))
    (threadPlacedOnSomeCore_dispatch_self st c tid) hActive h


/-- The relation reads only the object store and the scheduler slots, so a
transition touching neither carries it across. -/
theorem threadInactiveFlagConsistent_congr (st₁ st₂ : SystemState)
    (hObjs : st₂.objects = st₁.objects) (hSched : st₂.scheduler = st₁.scheduler)
    (h : threadInactiveFlagConsistent st₁) : threadInactiveFlagConsistent st₂ := by
  refine threadInactiveFlagConsistent_of_frame st₁ st₂ ?_ ?_ h
  · intro oid tcb' hObj
    exact ⟨tcb', by rw [hObjs] at hObj; exact hObj, rfl, rfl⟩
  · intro u
    exact threadPlacedOnSomeCore_congr st₁ st₂ u (fun c => by rw [hSched])
      (fun c => (SystemState.RunCoresAgree.of_objects hObjs).queuedOn c u)

/-- The preempt's placement frame, extracted so the dispatch composition can
use it without re-running the case analysis. -/
theorem preemptCurrentOnCore_threadPlacedOnSomeCore (st : SystemState) (c : CoreId)
    (incoming u : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) :
    threadPlacedOnSomeCore (preemptCurrentOnCore st c incoming) u
      = threadPlacedOnSomeCore st u := by
  unfold preemptCurrentOnCore
  split
  · rfl
  · rename_i prevTid hCur
    split
    · rfl
    · split
      · exact threadPlacedOnSomeCore_save_and_reenqueue st c prevTid u _ _ hObjInv hCur
      · rfl

/-- The preempt's store frame. -/
theorem preemptCurrentOnCore_objects_frame (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (oid : SeLe4n.ObjId) (tcb' : TCB)
    (hObj : (preemptCurrentOnCore st c incoming).objects[oid]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[oid]? = some (.tcb tcb) ∧
      tcb'.threadState = tcb.threadState ∧ tcb'.ipcState = tcb.ipcState := by
  revert hObj
  unfold preemptCurrentOnCore
  split
  · intro hObj; exact ⟨tcb', hObj, rfl, rfl⟩
  · rename_i prevTid _
    split
    · intro hObj; exact ⟨tcb', hObj, rfl, rfl⟩
    · split
      · rename_i prevTcb hPrev hW
        intro hObj
        obtain ⟨t0, h0, hE⟩ :=
          (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ c prevTid _).get_tcb' hObj
        have h0' : (st.objects.insert prevTid.toObjId
            (.tcb { prevTcb with registerContext := st.machine.regsOnCore c }))[oid]?
            = some (.tcb t0) := h0
        obtain ⟨tcb, hT, hS, hI⟩ := objects_insert_tcb_frame st prevTid.toObjId
          { prevTcb with registerContext := st.machine.regsOnCore c } prevTcb hObjInv
          ((SystemState.getTcb?_eq_some_iff st prevTid prevTcb).mp hPrev) rfl rfl oid t0 h0'
        exact ⟨tcb, hT, (TCB.proj_eq_of_withoutRunLinks_eq TCB.threadState hE).trans hS,
          (TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hE).trans hI⟩
      · intro hObj; exact ⟨tcb', hObj, rfl, rfl⟩


/-- The preempt leaves core `c`'s displaced current thread queued on some core:
on `c` when the enqueue admits it, and otherwise on the core its run-queue links
already name. -/
theorem preemptCurrentOnCore_outgoing_queued (st : SystemState) (c : CoreId)
    (tid u : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hu : u ≠ tid) (hCur : st.scheduler.currentOnCore c = some u)
    (hTcb : (st.getTcb? u).isSome) (hI : isIdleThreadId u = false) :
    threadQueuedOnSomeCore (preemptCurrentOnCore st c tid) u = true := by
  obtain ⟨prevTcb, hPrev⟩ := Option.isSome_iff_exists.mp hTcb
  rw [threadQueuedOnSomeCore_eq_true_iff]
  unfold preemptCurrentOnCore
  rw [hCur]
  dsimp only
  rw [if_neg (by simpa using hu), SystemState.getTcbWitnessed?_eq_some hPrev]
  dsimp only
  refine SystemState.runEnqueueOnCore_queuedOn_somewhere _ ?_ hI
  rw [SystemState.rewriteObject_tcb_getTcb?_self _ _ _ _ hObjInv]; rfl

/-- **WS-RR RR7.36**: the per-core context switch preserves the inactive-flag
relation.

Two side conditions, both real properties of the dispatch rather than proof
bookkeeping.  `hCurrentValid` says core `c`'s current slot resolves to a TCB —
the scheduler's own `currentThreadValid` — and it is what makes the preempt's
re-enqueue happen at all: without it the displaced thread is stranded off every
queue.  `hActive` says the state does not classify the incoming thread
`.Inactive`, which the run-queue selection establishes and which a dispatch of a
suspended thread would violate.  Neither can be dropped: they are the two ways
this relation breaks. -/
theorem switchToThreadOnCore_preserves_threadInactiveFlagConsistent
    (st st' : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hCurrentValid : ∀ u, st.scheduler.currentOnCore c = some u → (st.getTcb? u).isSome)
    (hActive : ∀ tcb, st.getTcb? tid = some tcb →
      inferThreadState st tid tcb ≠ .Inactive)
    (hStep : switchToThreadOnCore st c tid = .ok st')
    (h : threadInactiveFlagConsistent st) :
    threadInactiveFlagConsistent st' := by
  unfold switchToThreadOnCore at hStep
  split at hStep
  · split at hStep
    · -- The success arm.  Name the four intermediate states.
      have hEq : st' = { (restoreIncomingContextOnCoreUnlessCurrent
            ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid)
            c tid) with
          scheduler := (restoreIncomingContextOnCoreUnlessCurrent
            ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid)
            c tid).scheduler.setCurrentOnCore c (some tid) } := by
        exact (Except.ok.inj hStep).symm
      subst hEq
      -- The preempt carries the relation, and the dispatch step is applied to it.
      have hP : threadInactiveFlagConsistent (preemptCurrentOnCore st c tid) :=
        preemptCurrentOnCore_preserves_threadInactiveFlagConsistent st c tid hObjInv h
      have hOutgoing : ∀ u, u ≠ tid → isIdleThreadId u = false →
          (preemptCurrentOnCore st c tid).scheduler.currentOnCore c = some u →
          threadQueuedOnSomeCore (preemptCurrentOnCore st c tid) u = true := by
        intro u hu hI hCurP
        rw [preemptCurrentOnCore_currentOnCore] at hCurP
        exact preemptCurrentOnCore_outgoing_queued st c tid u hObjInv hu hCurP
          (hCurrentValid u hCurP) hI
      have hActiveP : ∀ tcb, (preemptCurrentOnCore st c tid).getTcb? tid = some tcb →
          inferThreadState (preemptCurrentOnCore st c tid) tid tcb ≠ .Inactive := by
        intro tcb hGet hInactive
        have hObj := (SystemState.getTcb?_eq_some_iff _ tid tcb).mp hGet
        obtain ⟨tcb₀, hPre, _, hIpc⟩ :=
          preemptCurrentOnCore_objects_frame st c tid hObjInv _ tcb hObj
        rw [inferThreadState_eq_inactive_iff,
          preemptCurrentOnCore_threadPlacedOnSomeCore _ _ _ _ hObjInv, hIpc] at hInactive
        exact hActive tcb₀ ((SystemState.getTcb?_eq_some_iff st tid tcb₀).mpr hPre)
          ((inferThreadState_eq_inactive_iff st tid tcb₀).mpr hInactive)
      have hDispatch := threadInactiveFlagConsistent_dispatch
        (preemptCurrentOnCore st c tid) c tid hOutgoing hActiveP hP
      refine threadInactiveFlagConsistent_congr _ _ ?_ ?_ hDispatch
      · exact restoreIncomingContextOnCoreUnlessCurrent_objects _ _ _
      · rw [restoreIncomingContextOnCoreUnlessCurrent_scheduler]
    · exact absurd hStep (by simp)
  · exact absurd hStep (by simp)


-- ============================================================================
-- WS-RR RR8.12 (Cut 4) / `v0.35.158` — the scheduling point and placement
-- ============================================================================
--
-- Two directions.  WS-RR RR8.12 (Cut 4) proved the switch keeps a *placed*
-- thread placed, for WS-OD OD1.7's wake of the cancellation reclaim's holder.
-- `v0.35.158` retired that wake — the reclaim now DESCHEDULES the holder it
-- unbinds, as every other donation pop does — and the payoff a user sees turned
-- around with it: a `.tcbSuspend` leaves the server its victim called on no
-- scheduler slot, *after the whole suspend pipeline*, whose last stage is a
-- scheduling point.  So the switch's scheduler shape is stated once
-- (`switchToThreadOnCore_ok_scheduler`) and both directions read it; the
-- composition is `suspendThreadOnCore_holder_unplaced` in
-- `IPC/CrossCore/Cancellation.lean`.  The placed direction is kept: it is what
-- the wake's consumers read and what the next placed-thread payoff will.

/-- `v0.35.158`: the switch's scheduler, read off a successful step — the
dispatch shape over the preempted state.  Extracted from the placement frame
below so the two placement directions (a placed thread stays placed; an unplaced
one stays unplaced) read one equation rather than each re-deriving the shape. -/
theorem switchToThreadOnCore_ok_scheduler (st st' : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hStep : switchToThreadOnCore st c tid = .ok st') :
    st'.scheduler = ({ (preemptCurrentOnCore st c tid).runRemoveOnCore c tid with
        scheduler := ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid).scheduler.setCurrentOnCore
            c (some tid) } : SystemState).scheduler := by
  unfold switchToThreadOnCore at hStep
  split at hStep
  · split at hStep
    · have hEq : st' = { (restoreIncomingContextOnCoreUnlessCurrent
            ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid)
            c tid) with
          scheduler := (restoreIncomingContextOnCoreUnlessCurrent
            ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid)
            c tid).scheduler.setCurrentOnCore c (some tid) } := by
        exact (Except.ok.inj hStep).symm
      subst hEq
      -- The switch's scheduler is the dispatch shape over the preempted state.
      have hSched : ({ (restoreIncomingContextOnCoreUnlessCurrent
            ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid)
            c tid) with
          scheduler := (restoreIncomingContextOnCoreUnlessCurrent
            ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid)
            c tid).scheduler.setCurrentOnCore c (some tid) } : SystemState).scheduler
          = ({ (preemptCurrentOnCore st c tid).runRemoveOnCore c tid with
                scheduler := ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid).scheduler.setCurrentOnCore
                    c (some tid) } : SystemState).scheduler := by
        show (restoreIncomingContextOnCoreUnlessCurrent _ c tid).scheduler.setCurrentOnCore
          c (some tid) = _
        rw [restoreIncomingContextOnCoreUnlessCurrent_scheduler]
      exact hSched
    · exact absurd hStep (by simp)
  · exact absurd hStep (by simp)

/-- The switch's object store, read off a successful step: the dispatch's, since
the incoming-context restore writes only the machine. -/
theorem switchToThreadOnCore_ok_objects (st st' : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hStep : switchToThreadOnCore st c tid = .ok st') :
    st'.objects = ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid).objects := by
  unfold switchToThreadOnCore at hStep
  split at hStep
  · split at hStep
    · rw [← Except.ok.inj hStep]
      exact restoreIncomingContextOnCoreUnlessCurrent_objects _ _ _
    · exact absurd hStep (by simp)
  · exact absurd hStep (by simp)

/-- A successful switch places every thread as its dispatch shape over the
preempted state does. -/
theorem switchToThreadOnCore_ok_threadPlacedOnSomeCore (st st' : SystemState) (c : CoreId)
    (tid u : SeLe4n.ThreadId) (hStep : switchToThreadOnCore st c tid = .ok st') :
    threadPlacedOnSomeCore st' u = threadPlacedOnSomeCore
      ({ (preemptCurrentOnCore st c tid).runRemoveOnCore c tid with
          scheduler := ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid).scheduler.setCurrentOnCore
            c (some tid) } : SystemState) u :=
  threadPlacedOnSomeCore_of_scheduler_eq _ _ u
    (switchToThreadOnCore_ok_scheduler st st' c tid hStep)
    (SystemState.RunCoresAgree.of_objects (switchToThreadOnCore_ok_objects st st' c tid hStep))

/-- **WS-RR RR8.12 (Cut 4)**: a context switch keeps a placed thread placed —
given that thread resolves to a TCB.

The hypothesis is not bookkeeping; it is the **one** way the switch can strand a
thread.  It is the side condition RR7.36 states for that same transition's
inactive-flag preservation, narrowed from *every thread current on `c`* to the
one thread this frame is about — which is all a per-thread frame can need.
`preemptCurrentOnCore` re-enqueues the outgoing thread only when its TCB
resolves — its `none` arm is the identity — and the `setCurrentOnCore` that
follows then displaces it with nothing to fall back to.  An idle thread is the
exception by design: the switch leaves it off every queue, as seL4 does. -/
theorem switchToThreadOnCore_preserves_threadPlacedOnSomeCore
    (st st' : SystemState) (c : CoreId) (tid u : SeLe4n.ThreadId)
    (hTcb : (st.getTcb? u).isSome) (hI : isIdleThreadId u = false)
    (hObjInv : st.objects.invExt)
    (hStep : switchToThreadOnCore st c tid = .ok st')
    (h : threadPlacedOnSomeCore st u = true) :
    threadPlacedOnSomeCore st' u = true := by
  rw [switchToThreadOnCore_ok_threadPlacedOnSomeCore st st' c tid u hStep]
  by_cases hu : u = tid
  · subst hu
    exact threadPlacedOnSomeCore_dispatch_self (preemptCurrentOnCore st c u) c u
  · rw [threadPlacedOnSomeCore_dispatch_ne (preemptCurrentOnCore st c tid) c tid u hu ?_,
      preemptCurrentOnCore_threadPlacedOnSomeCore _ _ _ _ hObjInv]
    · exact h
    · intro hCurP
      rw [preemptCurrentOnCore_currentOnCore] at hCurP
      exact preemptCurrentOnCore_outgoing_queued st c tid u hObjInv hu hCurP hTcb hI

/-- **`v0.35.158`**: the other direction — a context switch keeps an
**unplaced** thread unplaced, given it is not the thread being dispatched.

No resolvability side condition this time: the one way the switch can *place* a
thread is by dispatching it, and the thread it displaces was current, hence
placed, hence not this one.  The dispatched thread is the caller's to rule out —
`handleRescheduleSgiOnCore_preserves_unplaced` (`IPC/CrossCore/Cancellation.lean`)
does it from the chooser's own membership, which is why that half lives beside
the chooser's consumers rather than here. -/
theorem switchToThreadOnCore_preserves_unplaced
    (st st' : SystemState) (c : CoreId) (tid u : SeLe4n.ThreadId) (hu : u ≠ tid)
    (hObjInv : st.objects.invExt)
    (hStep : switchToThreadOnCore st c tid = .ok st')
    (h : threadPlacedOnSomeCore st u = false) :
    threadPlacedOnSomeCore st' u = false := by
  rw [switchToThreadOnCore_ok_threadPlacedOnSomeCore st st' c tid u hStep,
    threadPlacedOnSomeCore_dispatch_ne (preemptCurrentOnCore st c tid) c tid u hu ?_,
    preemptCurrentOnCore_threadPlacedOnSomeCore _ _ _ _ hObjInv]
  · exact h
  · intro hCurP
    rw [preemptCurrentOnCore_currentOnCore] at hCurP
    exfalso
    have hPlaced : threadPlacedOnSomeCore st u = true :=
      (threadPlacedOnSomeCore_eq_true_iff st u).mpr (Or.inl ⟨c, hCurP⟩)
    rw [h] at hPlaced
    exact Bool.false_ne_true hPlaced

/-- **WS-BP BP7.6**: the preempt adds to core `c`'s queue only the thread that
was current on `c` — so a thread neither queued nor current there before is not
queued there after. -/
theorem preemptCurrentOnCore_mem_runQueueOnCore_self (st : SystemState) (c : CoreId)
    (incoming u : SeLe4n.ThreadId)
    (h : u ∈ (preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c) :
    u ∈ st.scheduler.runQueueOnCore c ∨ st.scheduler.currentOnCore c = some u := by
  cases hCur : st.scheduler.currentOnCore c with
  | none =>
    left
    have hId : preemptCurrentOnCore st c incoming = st := by
      unfold preemptCurrentOnCore; rw [hCur]
    rw [hId] at h; exact h
  | some prev =>
    by_cases hEq : (prev == incoming) = true
    · left
      have hId : preemptCurrentOnCore st c incoming = st := by
        unfold preemptCurrentOnCore; rw [hCur]; dsimp only; rw [if_pos hEq]
      rw [hId] at h; exact h
    · cases hPT : st.getTcb? prev with
      | none =>
        left
        have hId : preemptCurrentOnCore st c incoming = st := by
          unfold preemptCurrentOnCore; rw [hCur]; dsimp only
          rw [if_neg hEq, SystemState.getTcbWitnessed?_eq_none hPT]
        rw [hId] at h; exact h
      | some ptcb =>
        unfold preemptCurrentOnCore at h; rw [hCur] at h; dsimp only at h
        rw [if_neg hEq, SystemState.getTcbWitnessed?_eq_some hPT] at h
        dsimp only at h
        rcases SystemState.runEnqueueOnCore_mem_runQueueOnCore_self h with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [h])

/-- **WS-BP BP7.6**: a context switch on core `c` makes no thread dispatchable
there except the one it dispatches.  Per-core, where
`switchToThreadOnCore_preserves_unplaced` is global: a thread that is queued on
another core is not unplaced, and is still not dispatchable on this one. -/
theorem switchToThreadOnCore_preserves_not_dispatchable_onCore
    (st st' : SystemState) (c : CoreId) (tid u : SeLe4n.ThreadId) (hu : u ≠ tid)
    (hStep : switchToThreadOnCore st c tid = .ok st')
    (hQ : u ∉ st.scheduler.runQueueOnCore c)
    (hC : st.scheduler.currentOnCore c ≠ some u) :
    u ∉ st'.scheduler.runQueueOnCore c ∧ st'.scheduler.currentOnCore c ≠ some u := by
  rw [switchToThreadOnCore_ok_scheduler st st' c tid hStep]
  refine ⟨?_, ?_⟩
  · show u ∉ (((preemptCurrentOnCore st c tid).runRemoveOnCore c tid).scheduler.setCurrentOnCore
          c (some tid)).runQueueOnCore c
    rw [SchedulerState.setCurrentOnCore_runQueueOnCore, SystemState.runRemoveOnCore_scheduler,
      SchedulerState.setRunQueueOnCore_runQueueOnCore_self, RunQueue.mem_remove]
    rintro ⟨hm, -⟩
    rcases preemptCurrentOnCore_mem_runQueueOnCore_self st c tid u hm with h | h
    · exact hQ h
    · exact hC h
  · show (((preemptCurrentOnCore st c tid).runRemoveOnCore c tid).scheduler.setCurrentOnCore
          c (some tid)).currentOnCore c ≠ some u
    rw [SchedulerState.setCurrentOnCore_currentOnCore_self]
    intro h; exact hu (Option.some.inj h).symm

/-- `v0.35.158`: placement is the resolver's `isSome` — the classification's
Boolean and `placedCoreOf?`'s witness are one question, so a consumer holding
`placedCoreOf? st u = none` reads "unplaced" in the vocabulary the suspend
pipeline's payoff is stated in. -/
theorem threadPlacedOnSomeCore_eq_isSome_placedCoreOf? (st : SystemState)
    (u : SeLe4n.ThreadId) :
    threadPlacedOnSomeCore st u = (placedCoreOf? st u).isSome := by
  rw [placedCoreOf?_isSome_iff]
  unfold threadPlacedOnSomeCore threadRunningOnSomeCore threadQueuedOnSomeCore
  exact Bool.or_comm _ _

-- `v0.35.158`: `handleRescheduleSgiOnCore_preserves_threadPlacedOnSomeCore` —
-- the per-core scheduling point keeps a placed thread placed — is retired with
-- `suspendThreadOnCore_holder_still_placed`, its only consumer.  The switch-level
-- fact it composed (`switchToThreadOnCore_preserves_threadPlacedOnSomeCore`,
-- above) stays, as the statement of the side condition under which a dispatch
-- keeps a placed thread placed; the unplaced direction the payoff reads now is
-- `handleRescheduleSgiOnCore_preserves_unplaced` (`IPC/CrossCore/Cancellation.lean`),
-- beside the chooser's membership fact it needs.

-- ============================================================================
-- WS-SM SM5.H — Per-core CBS (production operations)
-- ============================================================================
--
-- The per-core CBS replenishment-scheduling primitive, the SchedContext
-- replenishment migration, the run-queue migration, and the full
-- affinity-change-with-migration composite (the production transition the
-- `tcbSetAffinity` syscall dispatches).  The forward-looking theorem surface
-- lives in the staged `Scheduler/Operations/PerCoreCbs.lean`; these defs are
-- production-reached via the SM5.H.4 syscall (`setThreadCpuAffinityOp`).
--
-- `replenishOnCore` itself is defined earlier (just before
-- `timerTickBudgetOnCore`) because the live per-core budget tick now CALLS it
-- for its CBS replenishment write (so the primitive is genuinely load-bearing,
-- not merely proven-equal); see its def site for the docstring.

/-- WS-SM SM5.H.4 (plan §3.8): migrate SchedContext `scId`'s pending
replenishment from core `fromCore`'s release queue to core `toCore`'s, and a
no-op on self-migration.  WS-ZA ZA6.3: the run-time write is the context's own
link — unlinked from the source and linked into the destination at its sorted
place, at the release time the link holds, when the source's links queue it;
the abstract queues move with it (ghost, read off the pre-state's, no run-time
write): `scId`'s entries leave the source's and join the destination's at their
own times.  The two agree on every state whose release queues agree with the
contexts (`releaseQueueRefined`); stating the abstract move by the abstract
queues is what lets each abstract-queue fact about the migration (the moved
entries existed, the source keeps none) hold with no such hypothesis. -/
def migrateSchedContextReplenishment (st : SystemState) (scId : SchedContextId)
    (fromCore toCore : CoreId) : SystemState :=
  if fromCore = toCore then st
  else
    let st₁ := if st.releaseQueuedOn fromCore scId then
        (st.releaseRemoveOn fromCore scId).releaseInsertOn toCore scId (st.releaseAtOn fromCore scId)
      else st
    let fromQ := st.scheduler.replenishQueueOnCore fromCore
    let toQ := st.scheduler.replenishQueueOnCore toCore
    let moved := fromQ.entries.filter (fun e => e.1 == scId)
    let toQ' := moved.foldl (fun q e => q.insert scId e.2) toQ
    let sched := (st₁.scheduler.setReplenishQueueOnCore fromCore (fromQ.remove scId)).setReplenishQueueOnCore
      toCore toQ'
    { st₁ with scheduler := sched }

/-- WS-ZA ZA4.5: moving a thread between two cores' queues through its TCB
links writes the two queues as the abstract remove and insert, and each core's
ends. -/
theorem runMoveOnCore_scheduler (st : SystemState) (tid : SeLe4n.ThreadId)
    (fromCore toCore : CoreId) (p : SeLe4n.Priority) (h : fromCore ≠ toCore) :
    ((st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid p).scheduler =
      ((((st.scheduler.setRunQueueOnCore fromCore
          ((st.scheduler.runQueueOnCore fromCore).remove tid)).setRunQueueOnCore toCore
          ((st.scheduler.runQueueOnCore toCore).insert tid p)).setRunQueueEndsOnCore fromCore
          (st.runRemoveEnds fromCore tid)).setRunQueueEndsOnCore toCore
          ((st.runRemoveOnCore fromCore tid).runEnqueueEnds toCore tid p)) := by
  have hQ : (st.runRemoveOnCore fromCore tid).scheduler.runQueueOnCore toCore
      = st.scheduler.runQueueOnCore toCore := by
    simp [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ h]
  rw [SystemState.runEnqueueAdmitted_scheduler, hQ, SystemState.runRemoveOnCore_scheduler]
  rfl

/-- WS-SM SM5.H.4 (full thread migration): migrate thread `tid`'s **run-queue
entry** from core `fromCore` to core `toCore` on an affinity change.  When `tid`
is runnable on `fromCore` (`fromCore`'s run queue contains it), it is dequeued
there and re-enqueued on `toCore` at its effective priority; otherwise (blocked,
current, or already homed) it is a no-op.

This closes the wrong-core-dispatch gap: without it, a thread left on its old
core's run queue after a remote-affinity change would be selected by that core's
`chooseThreadOnCore` and dispatched by `scheduleEffectiveOnCore` (which does not
check affinity), running it on the wrong core.  Moving its run-queue entry
guarantees the affinity change can never strand a runnable thread on a core its
new affinity forbids. -/
def migrateRunQueueOnAffinityChange (st : SystemState) (tid : SeLe4n.ThreadId)
    (fromCore toCore : CoreId) : SystemState :=
  if fromCore = toCore then st
  else
    match st.getTcb? tid with
    | none => st
    | some tcb =>
      -- Its own run-queue links say whether it is queued on `fromCore` (seL4's
      -- `tcbQueued`); the abstract queue is ghost state (WS-ZA ZA4.5).
      if tcb.runCoreCode = fromCore.val + 1 then
        -- The thread leaves `fromCore`'s queue and joins `toCore`'s through its
        -- TCB run-queue links (WS-ZA ZA4.5).  The removal leaves it on no queue
        -- (its links named `fromCore`), so the enqueue is admitted.
        let stMoved := (st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid
          tcb.boostedPriority
        -- The reschedule-SGI accumulator (KSC-1): the insert on `toCore` is a
        -- wake there (the diff's queue rule); the removal from `fromCore`
        -- stales nothing.
        { stMoved with scheduler := stMoved.scheduler.markReschedulePendingOnCore toCore }
      else st

/-- WS-ZA ZA4.5: the run-queue migration touches the object store only in the
migrated thread's run-queue links and its neighbours'. -/
theorem migrateRunQueueOnAffinityChange_objectsAgreeOffRunLinks (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).objectsAgreeOffRunLinks st := by
  unfold migrateRunQueueOnAffinityChange
  split
  · exact .refl _
  · split
    · exact .refl _
    · split
      · exact (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ _ _ _).trans
          (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ _ _)
      · exact .refl _

/-- WS-SM SM5.H.4: the run-queue migration preserves `invExt` (its link writes
are in place). -/
theorem migrateRunQueueOnAffinityChange_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) (h : st.objects.invExt) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).objects.invExt := by
  unfold migrateRunQueueOnAffinityChange
  split
  · exact h
  · split
    · exact h
    · split
      · exact SystemState.runEnqueueAdmitted_objects_invExt _ _ _ _
          (SystemState.runRemoveOnCore_objects_invExt _ _ _ h)
      · exact h

/-- WS-SM SM5.H.4: the run-queue migration never advances the machine timer. -/
@[simp] theorem migrateRunQueueOnAffinityChange_machine (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).machine = st.machine := by
  unfold migrateRunQueueOnAffinityChange
  split
  · rfl
  · split
    · rfl
    · split
      · simp
      · rfl

/-- WS-SM SM5.H.4: the run-queue migration frames every core's **replenish** queue
(it writes only run-queue slots).

Declared in the **staged** `Scheduler/Operations/PerCoreCbs.lean` until
`v0.35.167`, where production could not read it; moved beside the definition it
frames, so the live `.tcbSetAffinity` arm's footprint can state that a thread on
no reservation moves no replenish entry. -/
@[simp] theorem migrateRunQueueOnAffinityChange_replenishQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore c' : CoreId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  unfold migrateRunQueueOnAffinityChange
  split
  · rfl
  · split
    · rfl
    · split
      · simp [SystemState.runEnqueueAdmitted_scheduler]
      · rfl

-- The reschedule-SGI accumulator (KSC-1): `runningCoreOf?` moved down once
-- more, to `Scheduler/Operations/Selection.lean`, so `markKeyChangeFor`
-- (`Scheduler/Operations/ReschedulePending.lean`) can read it from the
-- priority-inheritance writers, which this module's import chain
-- (`IPC/Operations/Timeout` → `PriorityInheritance/Propagate`) sits above.
-- Its qualified name is unchanged.

/-- WS-ZA ZA6.3 (the affinity stall, seL4's `remoteTCBStall`): an affinity change
that moves a thread **running** on its old home takes it off that core in the
same transition — the core's `current` slot is emptied and the core is flagged
to choose again (the diff's slot rule).  No register is read: on the executing
core the trap entry saved the caller's frame into its TCB
(`Architecture.saveCapturedSyscallFrame`), and a remote core saves its own frame
at its next entry (`Architecture.saveVacatedFrameOnCore`), which the HAL forces
before the change returns (`Concurrency.stallChangedCores`, the HAL's
`remote_stall`) and before which no other core resumes the thread
(`deferResidentElsewhere`).  The identity when the home does not move or the
thread is not running there. -/
def vacateForAffinityChange (st : SystemState) (tid : SeLe4n.ThreadId)
    (oldCore newCore : CoreId) : SystemState :=
  if oldCore ≠ newCore ∧ st.scheduler.currentOnCore oldCore = some tid then
    { st with scheduler :=
        (st.scheduler.setCurrentOnCore oldCore none).markReschedulePendingOnCore oldCore }
  else st

/-- WS-ZA ZA6.3: ...and the thread it took off its old home joins its new home's
run queue through its TCB links, a wake there (the diff's queue rule) — seL4's
`SCHED_APPEND` on the new affinity.  The guarded enqueue: a running thread is on
no queue, so its links admit it.  The identity when nothing was vacated. -/
def requeueVacatedOnNewHome (st : SystemState) (tid : SeLe4n.ThreadId) (newCore : CoreId)
    (vacated : Bool) : SystemState :=
  if vacated then
    match st.getTcb? tid with
    | some tcb =>
      let s := st.runEnqueueOnCore newCore tid tcb.boostedPriority
      { s with scheduler := s.scheduler.markReschedulePendingOnCore newCore }
    | none => st
  else st

/-- WS-ZA ZA6.3: does a core other than `home` run the thread?  The refusal the
affinity change keeps for a placement the kernel invariants rule out (every
running thread runs on its home, `currentDequeuedUniqueExcept.currentHome`), so
that a state outside them is left as it was rather than written through. -/
def affinityRunningElsewhere (st : SystemState) (tid : SeLe4n.ThreadId) (home : CoreId) :
    List CoreId → Bool
  | [] => false
  | c :: cs =>
    (st.scheduler.currentCode.get c == tid.val + 1 && c != home)
    || affinityRunningElsewhere st tid home cs

theorem affinityRunningElsewhere_eq (st : SystemState) (tid : SeLe4n.ThreadId) (home : CoreId)
    (cs : List CoreId) :
    cs.any (fun c => st.scheduler.currentOnCore c == some tid && c != home) =
      affinityRunningElsewhere st tid home cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [affinityRunningElsewhere]
    rw [List.any_cons, ← ih, currentOnCore_beq_some]

/-- A thread the search clears runs on no core but `home`. -/
theorem affinityRunningElsewhere_false {st : SystemState} {tid : SeLe4n.ThreadId}
    {home : CoreId} (h : affinityRunningElsewhere st tid home SeLe4n.Kernel.Concurrency.allCores = false)
    (c : CoreId) (hc : st.scheduler.currentOnCore c = some tid) : c = home := by
  rw [← affinityRunningElsewhere_eq, List.any_eq_false] at h
  have := h c (List.mem_finRange c)
  simp only [hc, beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq, Decidable.not_not] at this
  exact this

/-- WS-SM SM5.H.4 (plan §3.8, full thread migration): set a thread's CPU affinity
**and** migrate everything that follows the thread to its new home core — its
bound SchedContext's pending replenishments (`migrateSchedContextReplenishment`)
**and** its run-queue entry (`migrateRunQueueOnAffinityChange`) — emitting a
cross-core `.reschedule` SGI when the new home is remote from the executing core
and the thread is now runnable there (mirroring SM5.C's `wakeThread` cross-core
protocol).

**A running thread is moved too (WS-ZA ZA6.3, seL4's `remoteTCBStall`).**  A
thread current on its old home whose home moves is taken off that core in the
same transition (`vacateForAffinityChange`) and queued on its new home
(`requeueVacatedOnNewHome`), so at every committed state a thread current on
core `c` or queued on `c` is homed on `c`
(`currentDequeuedUniqueExcept.currentHome` / `queuedHome`).  This replaced the
`.threadOnDifferentCore` refusal of a running thread whose new affinity forbade
its core, and closed the case that refusal let through: unpinning a thread
running on a secondary core, which left it running there homed on the boot core
— so its exhausted budget was queued on a core its home did not name.  The
refusal kept is for a thread running on a core other than its old home, which
the invariant rules out (`affinityRunningElsewhere`).

Each core's idle thread is refused (`.invalidArgument`): it is pinned to its
core, never queued, and no affinity of another core is one it can take.

`oldCore` / `newCore` are the thread's home core before / after the affinity
write.  Unbound threads (`schedContextBinding.scId? = none`) have no
replenishments to migrate.  Fail-closed (`.invalidArgument`) on a non-TCB
target.  Returns the post-migration state paired with the optional SGI; the
syscall path (`setThreadCpuAffinityOp`) commits the state (the SGI firing is the
SM5.I FFI seam, exactly as SM5.C/D/F).

**Authority (security contract).**  The op performs **no** in-op capability check;
authority is the dispatch-layer write-capability gate on the target TCB
(`syscallRequiredRight .tcbSetAffinity = .write`, identical to `tcbSetPriority`).
A caller reaching this op already holds `.write` on the target via
`syscallLookupCap`. -/
def setThreadCpuAffinityWithMigration (st : SystemState) (targetTid : SeLe4n.ThreadId)
    (affinity : Option CoreId) (executingCore : CoreId) :
    Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  match st.getTcb? targetTid with
  | some tcb =>
      -- PR #889 review round 20: a core the platform does not have is not a
      -- home (RR5's `bootAffinitiesDeclared` relation on the live path).
      if affinity.any (fun c => c.val ≥ st.machine.declaredCoreCount) then
        .error .invalidArgument
      else if isIdleThreadId targetTid then .error .invalidArgument
      else
      let oldCore := determineTargetCore st targetTid
      if affinityRunningElsewhere st targetTid oldCore SeLe4n.Kernel.Concurrency.allCores then
        .error .threadOnDifferentCore
      else
      let newCore := affinity.getD bootCoreId
      let vacated := decide (oldCore ≠ newCore ∧ st.scheduler.currentOnCore oldCore = some targetTid)
      match setThreadCpuAffinity (vacateForAffinityChange st targetTid oldCore newCore)
          targetTid affinity with
      | .ok stSet =>
          let st1 := match tcb.schedContextBinding.scId? with
            | some scId => migrateSchedContextReplenishment stSet scId oldCore newCore
            | none => stSet
          let st2 := migrateRunQueueOnAffinityChange st1 targetTid oldCore newCore
          let st3 := requeueVacatedOnNewHome st2 targetTid newCore vacated
          let sgi : Option (CoreId × SgiKind) :=
            if newCore == executingCore then none
            else if st3.queuedOn newCore targetTid then
              some (newCore, SgiKind.reschedule)
            else none
          .ok (st3, sgi)
      | .error e => .error e
  | none => .error .invalidArgument

/-- WS-SM SM5.H.4: decode a `tcbSetAffinity` argument register into a target
affinity.  Values `0 .. numCores-1` bind the thread to that core; the dedicated
marker `numCores` (= `affinityUnbindMarker`) unbinds it (homed on the boot core); any
larger value is rejected with `.invalidArgument`.  The validated decode the
syscall dispatch uses. -/
def affinityUnbindMarker : Nat := SeLe4n.Kernel.Concurrency.numCores

/-- WS-SM SM5.H.4: the affinity argument decoder (see `affinityUnbindMarker`). -/
def decodeAffinity (v : Nat) : Except KernelError (Option CoreId) :=
  if h : v < SeLe4n.Kernel.Concurrency.numCores then .ok (some ⟨v, h⟩)
  else if v = affinityUnbindMarker then .ok none
  else .error .invalidArgument

/-- **WS-SM SM8.B (PR #861 review round 37): the per-core affinity op.**

The eighth boot-pinned live arm, and the first found by the *widened* routing
gate rather than by a review round: `setThreadCpuAffinityOp` below hardcoded
`bootCoreId` as the executing core and then discarded the SGI the migration
computed.  The old gate could not see it because its primitive list was
hand-written and omitted composite per-core operations; the derived reach test
finds it.

Inert on the live path today, and the reason is worth stating rather than
assuming: `executingCore` feeds **only** the returned SGI (the committed state
`st2` does not depend on it), the op dropped that SGI, and the dispatch entry
re-derives cross-core pokes from the `(pre, post)` diff keyed on the *real*
executing core — a migration leaves the thread newly queued on a home core it
was not queued on before, so `crossCoreSgiBody`'s queue rule fires.  So no poke
was lost.  What was wrong is that the value was computed against the wrong core
and then thrown away, which is a defect waiting for its first consumer.

This form threads the real core and returns the SGI. -/
def setThreadCpuAffinityOnCore (st : SystemState) (vTargetTid : ValidThreadId)
    (affinity : Option CoreId) (executingCore : CoreId) :
    Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  setThreadCpuAffinityWithMigration st vTargetTid.val affinity executingCore

/-- WS-SM SM5.H.4 (the `tcbSetAffinity` state effect): set a thread's CPU
affinity and migrate it to its new home core, the state effect of
`setThreadCpuAffinityWithMigration`.

The **boot-core instance** of `setThreadCpuAffinityOnCore`, retained under its
original name and signature so every theorem and test about it stands unchanged.
No longer on the live path: round 37 rerouted `dispatchCapabilityOnly
.tcbSetAffinity` through the per-core form, since the old body's claim that "the
executing core is the boot core in the single-core dispatch model" stopped being
true when the dispatch learned its real core. -/
def setThreadCpuAffinityOp (st : SystemState) (vTargetTid : ValidThreadId)
    (affinity : Option CoreId) : Except KernelError SystemState :=
  match setThreadCpuAffinityOnCore st vTargetTid affinity bootCoreId with
  | .ok (st', _) => .ok st'
  | .error e => .error e

/-- WS-SM SM8.B: the committed state does not depend on the executing core —
`executingCore` reaches only the returned SGI.  This is what makes rerouting the
live arm trace-safe, and it is a theorem rather than a reading of the body. -/
theorem setThreadCpuAffinityOnCore_state_core_independent (st : SystemState)
    (vTargetTid : ValidThreadId) (affinity : Option CoreId) (c₁ c₂ : CoreId) :
    (setThreadCpuAffinityOnCore st vTargetTid affinity c₁).map Prod.fst
      = (setThreadCpuAffinityOnCore st vTargetTid affinity c₂).map Prod.fst := by
  unfold setThreadCpuAffinityOnCore setThreadCpuAffinityWithMigration
  dsimp only
  repeat' (first | rfl | split)

/-- WS-SM SM8.B: and hence the retained boot-core op agrees with the per-core
form on the state, at **every** executing core. -/
theorem setThreadCpuAffinityOp_eq_onCore_state (st : SystemState)
    (vTargetTid : ValidThreadId) (affinity : Option CoreId) (executingCore : CoreId) :
    setThreadCpuAffinityOp st vTargetTid affinity
      = (setThreadCpuAffinityOnCore st vTargetTid affinity executingCore).map Prod.fst := by
  unfold setThreadCpuAffinityOp
  rw [← setThreadCpuAffinityOnCore_state_core_independent st vTargetTid affinity
        bootCoreId executingCore]
  cases setThreadCpuAffinityOnCore st vTargetTid affinity bootCoreId <;> rfl

-- ============================================================================
-- WS-ZA ZA5.2: the affinity write in its slot
-- ============================================================================

/-- WS-ZA ZA5.2: the `v`-th entry of a list of cores already wrapped in `some`,
returned as the list's own cell (`none` past the end), so a decoded affinity is
never built. -/
def nthCoreSome : Nat → List (Option CoreId) → Option CoreId
  | _, [] => none
  | 0, o :: _ => o
  | n + 1, _ :: os => nthCoreSome n os

theorem nthCoreSome_allCoresSome (v : Nat) (h : v < SeLe4n.Kernel.Concurrency.numCores) :
    nthCoreSome v allCoresSome = some ⟨v, h⟩ := by
  have h4 : SeLe4n.Kernel.Concurrency.numCores = 4 := rfl
  rcases v with _ | _ | _ | _ | v
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd h (by rw [h4]; omega)

/-- WS-ZA ZA5.2: `decodeAffinity` in continuation form: the decoded affinity is
handed to `k` (the bound core drawn from `allCoresSome`), a refusal to `err`, so
neither an `Except` nor a `some` is built (`decodeAffinityK_eq`). -/
@[inline] def decodeAffinityK {α : Type} (v : Nat) (k : Option CoreId → α)
    (err : KernelError → α) : α :=
  if v < SeLe4n.Kernel.Concurrency.numCores then k (nthCoreSome v allCoresSome)
  else if v = affinityUnbindMarker then k none
  else err .invalidArgument

theorem decodeAffinityK_eq {α : Type} (v : Nat) (k : Option CoreId → α)
    (err : KernelError → α) :
    decodeAffinityK v k err =
      (match decodeAffinity v with
       | .ok a => k a
       | .error e => err e) := by
  unfold decodeAffinityK decodeAffinity
  by_cases h : v < SeLe4n.Kernel.Concurrency.numCores
  · simp only [h, dif_pos, if_pos, nthCoreSome_allCoresSome v h]
  · simp only [h, dif_neg, if_neg, not_false_eq_true]
    split <;> rfl

/-- WS-ZA ZA5.2: the checks `setThreadCpuAffinityWithMigration` makes, asked
before any write: the target is a TCB found in its slot, a bound core is one the
platform declares, the target is no idle thread, and the thread runs on no core
but its home.  When they pass the operation's state is `setAffinityPerform`
(`setThreadCpuAffinityOnCore_of_admitted`). -/
@[inline] def setAffinityAdmitted (st : SystemState) (tid : SeLe4n.ThreadId)
    (affinity : Option CoreId) : Bool :=
  match st.getTcb? tid with
  | none => false
  | some _ =>
    st.objects.findsInPlace tid.toObjId
    && !(match affinity with
         | some c => decide (c.val ≥ st.machine.declaredCoreCount)
         | none => false)
    && !isIdleThreadId tid
    && !affinityRunningElsewhere st tid (determineTargetCore st tid)
      SeLe4n.Kernel.Concurrency.allCores

/-- WS-ZA ZA5.2: the affinity change once admitted.  Every read (the old home,
the bound scheduling context, whether the thread runs there) comes before the
write; a thread running on its old home is taken off it (WS-ZA ZA6.3), the TCB
is rewritten in its slot, and then the replenishments and the run-queue entry
follow the thread to its new home, as `setThreadCpuAffinityWithMigration`. -/
def setAffinityPerform (st : SystemState) (tid : SeLe4n.ThreadId)
    (affinity : Option CoreId) : SystemState :=
  let oldCore := determineTargetCore st tid
  let newCore := affinity.getD bootCoreId
  match st.getTcb? tid with
  | none => st
  | some tcb =>
    let vacated := decide (oldCore ≠ newCore ∧ st.scheduler.currentOnCore oldCore = some tid)
    let st1 := (vacateForAffinityChange st tid oldCore newCore).updateTcb tid
      (fun t => { t with cpuAffinity := affinity })
    let st2 := match tcb.schedContextBinding.scId? with
      | some scId => migrateSchedContextReplenishment st1 scId oldCore newCore
      | none => st1
    requeueVacatedOnNewHome (migrateRunQueueOnAffinityChange st2 tid oldCore newCore) tid
      newCore vacated

/-- The vacate writes the scheduler alone. -/
@[simp] theorem vacateForAffinityChange_objects (st : SystemState) (tid : SeLe4n.ThreadId)
    (oldCore newCore : CoreId) :
    (vacateForAffinityChange st tid oldCore newCore).objects = st.objects := by
  unfold vacateForAffinityChange; split <;> rfl

@[simp] theorem vacateForAffinityChange_machine (st : SystemState) (tid : SeLe4n.ThreadId)
    (oldCore newCore : CoreId) :
    (vacateForAffinityChange st tid oldCore newCore).machine = st.machine := by
  unfold vacateForAffinityChange; split <;> rfl

theorem vacateForAffinityChange_getTcb? (st : SystemState) (tid : SeLe4n.ThreadId)
    (oldCore newCore : CoreId) (t : SeLe4n.ThreadId) :
    (vacateForAffinityChange st tid oldCore newCore).getTcb? t = st.getTcb? t := by
  unfold SystemState.getTcb?; rw [vacateForAffinityChange_objects]

/-- The vacate and the requeue write no replenish queue. -/
@[simp] theorem vacateForAffinityChange_replenishQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (oldCore newCore c : CoreId) :
    (vacateForAffinityChange st tid oldCore newCore).scheduler.replenishQueueOnCore c =
      st.scheduler.replenishQueueOnCore c := by
  unfold vacateForAffinityChange; split <;> simp

@[simp] theorem requeueVacatedOnNewHome_replenishQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (newCore c : CoreId) (vacated : Bool) :
    (requeueVacatedOnNewHome st tid newCore vacated).scheduler.replenishQueueOnCore c =
      st.scheduler.replenishQueueOnCore c := by
  unfold requeueVacatedOnNewHome
  split
  · split
    · simp only [SchedulerState.markReschedulePendingOnCore_replenishQueueOnCore,
        SystemState.runEnqueueOnCore_replenishQueueOnCore]
    · rfl
  · rfl

/-- The requeue touches the object store only in the requeued thread's
run-queue links and its neighbours'. -/
theorem requeueVacatedOnNewHome_objectsAgreeOffRunLinks (st : SystemState)
    (tid : SeLe4n.ThreadId) (newCore : CoreId) (vacated : Bool) :
    (requeueVacatedOnNewHome st tid newCore vacated).objectsAgreeOffRunLinks st := by
  unfold requeueVacatedOnNewHome
  split
  · split
    · exact SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _
    · exact .refl _
  · exact .refl _

theorem requeueVacatedOnNewHome_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (newCore : CoreId) (vacated : Bool) (h : st.objects.invExt) :
    (requeueVacatedOnNewHome st tid newCore vacated).objects.invExt := by
  unfold requeueVacatedOnNewHome
  split
  · split
    · exact SystemState.runEnqueueOnCore_objects_invExt _ _ _ _ h
    · exact h
  · exact h

@[simp] theorem requeueVacatedOnNewHome_machine (st : SystemState)
    (tid : SeLe4n.ThreadId) (newCore : CoreId) (vacated : Bool) :
    (requeueVacatedOnNewHome st tid newCore vacated).machine = st.machine := by
  unfold requeueVacatedOnNewHome
  split
  · split
    · simp
    · rfl
  · rfl

theorem vacateForAffinityChange_objectsAgreeOffRunLinks (st : SystemState)
    (tid : SeLe4n.ThreadId) (oldCore newCore : CoreId) :
    (vacateForAffinityChange st tid oldCore newCore).objectsAgreeOffRunLinks st := by
  intro x; rw [vacateForAffinityChange_objects]

@[simp] theorem vacateForAffinityChange_determineTargetCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (oldCore newCore : CoreId) (t : SeLe4n.ThreadId) :
    determineTargetCore (vacateForAffinityChange st tid oldCore newCore) t =
      determineTargetCore st t :=
  determineTargetCore_of_objectsAgreeOffRunLinks
    (vacateForAffinityChange_objectsAgreeOffRunLinks st tid oldCore newCore) t

@[simp] theorem vacateForAffinityChange_getSchedContext? (st : SystemState)
    (tid : SeLe4n.ThreadId) (oldCore newCore : CoreId) (s : SeLe4n.SchedContextId) :
    (vacateForAffinityChange st tid oldCore newCore).getSchedContext? s =
      st.getSchedContext? s := by
  unfold SystemState.getSchedContext?; rw [vacateForAffinityChange_objects]

/-- The vacate writes only `oldCore`'s `current` slot and reschedule flag. -/
@[simp] theorem vacateForAffinityChange_runQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (oldCore newCore c : CoreId) :
    (vacateForAffinityChange st tid oldCore newCore).scheduler.runQueueOnCore c =
      st.scheduler.runQueueOnCore c := by
  unfold vacateForAffinityChange; split <;> simp

/-- The vacate keeps every run queue's agreement with the threads. -/
theorem vacateForAffinityChange_runQueueRefined {st : SystemState} {tid : SeLe4n.ThreadId}
    {oldCore newCore : CoreId} (h : st.runQueueRefined) :
    (vacateForAffinityChange st tid oldCore newCore).runQueueRefined :=
  SystemState.runQueueRefined_of_frame
    (fun c t => SystemState.runLinkOn_of_objects (vacateForAffinityChange_objects _ _ _ _) c t)
    (by unfold vacateForAffinityChange; split <;> rfl)
    (by unfold vacateForAffinityChange; split <;> rfl) h

/-- The affinity run-queue migration repoints no core's `current` slot. -/
@[simp] theorem migrateRunQueueOnAffinityChange_currentOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore c' : CoreId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  unfold migrateRunQueueOnAffinityChange
  split
  · rfl
  · split
    · rfl
    · split <;> simp

/-- Where the migration leaves a thread: the migrated one, if its links named
`fromCore`, on `toCore` alone; every other where it was. -/
theorem migrateRunQueueOnAffinityChange_queuedOn (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore c : CoreId) (y : SeLe4n.ThreadId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).queuedOn c y =
      if y = tid ∧ fromCore ≠ toCore ∧ st.queuedOn fromCore tid = true then decide (c = toCore)
      else st.queuedOn c y := by
  unfold migrateRunQueueOnAffinityChange
  split
  · rename_i hft; rw [if_neg (fun h => h.2.1 hft)]
  · rename_i hft
    split
    · rename_i hT
      have hq : st.queuedOn fromCore tid = false := by unfold SystemState.queuedOn; rw [hT]
      rw [if_neg (fun h => by rw [hq] at h; exact absurd h.2.2 (by simp))]
    · rename_i tcb hT
      split
      · rename_i hC
        have hq : st.queuedOn fromCore tid = true := by
          unfold SystemState.queuedOn; simp [hT, hC]
        show ((st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid
          tcb.boostedPriority).queuedOn c y = _
        rw [SystemState.runEnqueueAdmitted_queuedOn, SystemState.runRemoveOnCore_queuedOn]
        by_cases hy : y = tid
        · subst hy
          rw [if_pos rfl, if_pos ⟨rfl, hft, hq⟩, SystemState.runRemoveOnCore_getTcb?_isSome, hT]
          simp
        · rw [if_neg hy, if_neg (fun h => hy h.1), if_neg (fun h => hy h.1)]
      · rename_i hC
        have hq : st.queuedOn fromCore tid = false := by
          unfold SystemState.queuedOn; simp [hT, hC]
        rw [if_neg (fun h => by rw [hq] at h; exact absurd h.2.2 (by simp))]

@[simp] theorem requeueVacatedOnNewHome_currentOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (newCore : CoreId) (vacated : Bool) (c : CoreId) :
    (requeueVacatedOnNewHome st tid newCore vacated).scheduler.currentOnCore c =
      st.scheduler.currentOnCore c := by
  unfold requeueVacatedOnNewHome
  split
  · split
    · simp
    · rfl
  · rfl

/-- The requeue moves no thread but the requeued one... -/
theorem requeueVacatedOnNewHome_queuedOn_ne (st : SystemState)
    (tid : SeLe4n.ThreadId) (newCore : CoreId) (vacated : Bool) (c : CoreId)
    (y : SeLe4n.ThreadId) (hy : y ≠ tid) :
    (requeueVacatedOnNewHome st tid newCore vacated).queuedOn c y = st.queuedOn c y := by
  unfold requeueVacatedOnNewHome
  split
  · split
    · show (st.runEnqueueOnCore newCore tid _).queuedOn c y = _
      rw [SystemState.runEnqueueOnCore_queuedOn, if_neg (fun h => hy h.1)]
    · rfl
  · rfl

/-- ...and that one only onto its new home, and only when it was vacated. -/
theorem requeueVacatedOnNewHome_queuedOn_self (st : SystemState)
    (tid : SeLe4n.ThreadId) (newCore : CoreId) (vacated : Bool) (c : CoreId)
    (h : (requeueVacatedOnNewHome st tid newCore vacated).queuedOn c tid = true) :
    (vacated = true ∧ c = newCore) ∨ st.queuedOn c tid = true := by
  unfold requeueVacatedOnNewHome at h
  split at h
  · rename_i hV
    split at h
    · change (st.runEnqueueOnCore newCore tid _).queuedOn c tid = true at h
      rw [SystemState.runEnqueueOnCore_queuedOn] at h
      split at h
      · exact .inl ⟨hV, of_decide_eq_true h⟩
      · exact .inr h
    · exact .inr h
  · exact .inr h

/-- Which `current` slot the vacate empties. -/
theorem vacateForAffinityChange_currentOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (oldCore newCore c : CoreId) :
    (vacateForAffinityChange st tid oldCore newCore).scheduler.currentOnCore c =
      if c = oldCore ∧ oldCore ≠ newCore ∧ st.scheduler.currentOnCore oldCore = some tid then none
      else st.scheduler.currentOnCore c := by
  unfold vacateForAffinityChange
  split
  · rename_i h
    simp only [SchedulerState.markReschedulePendingOnCore_currentOnCore]
    by_cases hc : c = oldCore
    · subst hc; rw [SchedulerState.setCurrentOnCore_currentOnCore_self, if_pos ⟨rfl, h⟩]
    · rw [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc),
        if_neg (fun h' => hc h'.1)]
  · rename_i h
    rw [if_neg (fun h' => h h'.2)]

/-- The affinity write replaces the target's TCB by the same TCB with the new
affinity, and no other. -/
theorem setThreadCpuAffinity_getTcb?_view {s s' : SystemState} {t : SeLe4n.ThreadId}
    {a : Option CoreId} {tcb : TCB} (hInv : s.objects.invExt) (hT : s.getTcb? t = some tcb)
    (hSet : setThreadCpuAffinity s t a = .ok s') :
    s'.getTcb? t = some { tcb with cpuAffinity := a } ∧
      (∀ u, u ≠ t → s'.getTcb? u = s.getTcb? u) ∧ s'.scheduler = s.scheduler := by
  unfold setThreadCpuAffinity at hSet
  rw [SystemState.getTcbWitnessed?_eq_some hT] at hSet
  simp only [Except.ok.injEq] at hSet
  subst hSet
  exact ⟨SystemState.rewriteObject_tcb_getTcb?_self _ _ _ _ hInv,
    fun u hu => SystemState.rewriteObject_getTcb?_ne _ _ _ _ hInv u
      (fun h => hu (ThreadId.toObjId_injective _ _ h).symm), rfl⟩

/-- **Where the affinity change leaves every thread**, from the state after the
affinity write and the replenishment move (`st1`): the `current` slots are the
vacate's, every other thread is as it was off its run-queue links, the target's
TCB is its old one with the new affinity, no other thread changes queue, and the
target ends queued only on its new home or where it already was off its old
home — and only newly so if it was queued on or running on the home it left. -/
theorem affinityChange_placement_of_mid {st st1 : SystemState} {t : SeLe4n.ThreadId}
    {tcb : TCB} {affinity : Option CoreId} {old new : CoreId}
    (hT : st.getTcb? t = some tcb)
    (hT1 : st1.getTcb? t = some { tcb with cpuAffinity := affinity })
    (hT1' : ∀ u, u ≠ t → st1.getTcb? u = st.getTcb? u)
    (hC1 : ∀ c, st1.scheduler.currentOnCore c =
      (vacateForAffinityChange st t old new).scheduler.currentOnCore c) :
    let st' := requeueVacatedOnNewHome (migrateRunQueueOnAffinityChange st1 t old new) t new
      (decide (old ≠ new ∧ st.scheduler.currentOnCore old = some t))
    (∀ c, st'.scheduler.currentOnCore c =
      (vacateForAffinityChange st t old new).scheduler.currentOnCore c) ∧
    (∀ u, u ≠ t → (st'.getTcb? u).map TCB.withoutRunLinks = (st.getTcb? u).map TCB.withoutRunLinks) ∧
    (st'.getTcb? t).map TCB.withoutRunLinks =
      some ({ tcb with cpuAffinity := affinity }).withoutRunLinks ∧
    (∀ c u, u ≠ t → st'.queuedOn c u = st.queuedOn c u) ∧
    (∀ c, st'.queuedOn c t = true → c = new ∨ (c ≠ old ∧ st.queuedOn c t = true)) ∧
    (∀ c, st'.queuedOn c t = true → st.queuedOn c t = true ∨
      (old ≠ new ∧ (st.queuedOn old t = true ∨ st.scheduler.currentOnCore old = some t))) := by
  intro st'
  have hA : st'.objectsAgreeOffRunLinks st1 :=
    (requeueVacatedOnNewHome_objectsAgreeOffRunLinks _ _ _ _).trans
      (migrateRunQueueOnAffinityChange_objectsAgreeOffRunLinks _ _ _ _)
  have hQ1 : ∀ c u, st1.queuedOn c u = st.queuedOn c u := by
    intro c u
    by_cases hu : u = t
    · subst hu; unfold SystemState.queuedOn; rw [hT1, hT]
    · exact SystemState.queuedOn_of_getTcb? (hT1' u hu) c
  refine ⟨fun c => ?_, fun u hu => ?_, ?_, fun c u hu => ?_, fun c hq => ?_, fun c hq => ?_⟩
  · show (requeueVacatedOnNewHome _ _ _ _).scheduler.currentOnCore c = _
    rw [requeueVacatedOnNewHome_currentOnCore, migrateRunQueueOnAffinityChange_currentOnCore, hC1]
  · rw [hA.getTcb? u, hT1' u hu]
  · rw [hA.getTcb? t, hT1]; rfl
  · show (requeueVacatedOnNewHome _ _ _ _).queuedOn c u = _
    rw [requeueVacatedOnNewHome_queuedOn_ne _ _ _ _ _ _ hu,
      migrateRunQueueOnAffinityChange_queuedOn, if_neg (fun h => hu h.1), hQ1]
  · rcases requeueVacatedOnNewHome_queuedOn_self _ _ _ _ _ hq with ⟨-, hc⟩ | hq2
    · exact .inl hc
    · rw [migrateRunQueueOnAffinityChange_queuedOn] at hq2
      split at hq2
      · exact .inl (of_decide_eq_true hq2)
      · rename_i hn
        rw [hQ1] at hq2
        by_cases hc : c = old
        · by_cases hon : old = new
          · exact .inl (hc.trans hon)
          · exact absurd ⟨rfl, hon, by rw [hQ1, ← hc]; exact hq2⟩ hn
        · exact .inr ⟨hc, hq2⟩
  · rcases requeueVacatedOnNewHome_queuedOn_self _ _ _ _ _ hq with ⟨hV, -⟩ | hq2
    · have hV' := of_decide_eq_true hV
      exact .inr ⟨hV'.1, .inr hV'.2⟩
    · rw [migrateRunQueueOnAffinityChange_queuedOn] at hq2
      split at hq2
      · rename_i hcnd
        exact .inr ⟨hcnd.2.1, .inl (by rw [← hQ1]; exact hcnd.2.2)⟩
      · rw [hQ1] at hq2; exact .inl hq2

/-- **The shape of a committed affinity change**: every check passed, the
affinity write on the vacated state succeeded, and the committed state is the
requeue over the run-queue and replenishment migrations — the one inversion the
frame, footprint and noninterference proofs share. -/
theorem setThreadCpuAffinityWithMigration_ok_shape {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {affinity : Option CoreId} {executingCore : CoreId}
    {sgi : Option (CoreId × SgiKind)}
    (h : setThreadCpuAffinityWithMigration st tid affinity executingCore = .ok (st', sgi)) :
    ∃ tcb stSet, st.getTcb? tid = some tcb ∧
      affinity.any (fun c => c.val ≥ st.machine.declaredCoreCount) = false ∧
      isIdleThreadId tid = false ∧
      affinityRunningElsewhere st tid (determineTargetCore st tid)
        SeLe4n.Kernel.Concurrency.allCores = false ∧
      setThreadCpuAffinity (vacateForAffinityChange st tid (determineTargetCore st tid)
        (affinity.getD bootCoreId)) tid affinity = .ok stSet ∧
      st' = requeueVacatedOnNewHome (migrateRunQueueOnAffinityChange
        (match tcb.schedContextBinding.scId? with
          | some scId => migrateSchedContextReplenishment stSet scId
              (determineTargetCore st tid) (affinity.getD bootCoreId)
          | none => stSet) tid (determineTargetCore st tid) (affinity.getD bootCoreId)) tid
        (affinity.getD bootCoreId)
        (decide (determineTargetCore st tid ≠ affinity.getD bootCoreId ∧
          st.scheduler.currentOnCore (determineTargetCore st tid) = some tid)) ∧
      sgi = (if affinity.getD bootCoreId == executingCore then none
        else if st'.queuedOn (affinity.getD bootCoreId) tid then
          some (affinity.getD bootCoreId, SgiKind.reschedule)
        else none) := by
  unfold setThreadCpuAffinityWithMigration at h
  cases hT : st.getTcb? tid with
  | none => rw [hT] at h; exact absurd h (by simp)
  | some tcb =>
    rw [hT] at h
    have hD : affinity.any (fun c => c.val ≥ st.machine.declaredCoreCount) = false := by
      cases hd : affinity.any (fun c => c.val ≥ st.machine.declaredCoreCount)
      · rfl
      · rw [hd] at h; exact absurd h (by simp)
    have hI : isIdleThreadId tid = false := by
      cases hi : isIdleThreadId tid
      · rfl
      · rw [hD, hi] at h; exact absurd h (by simp)
    have hR : affinityRunningElsewhere st tid (determineTargetCore st tid)
        SeLe4n.Kernel.Concurrency.allCores = false := by
      cases hr : affinityRunningElsewhere st tid (determineTargetCore st tid)
          SeLe4n.Kernel.Concurrency.allCores
      · rfl
      · rw [hD, hI] at h; simp only [Bool.false_eq_true, ↓reduceIte, hr] at h
        exact absurd h (by simp)
    rw [hD, hI] at h
    simp only [Bool.false_eq_true, ↓reduceIte, hR] at h
    cases hSet : setThreadCpuAffinity (vacateForAffinityChange st tid
        (determineTargetCore st tid) (affinity.getD bootCoreId)) tid affinity with
    | error e => rw [hSet] at h; exact absurd h (by simp)
    | ok stSet =>
      rw [hSet] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      exact ⟨tcb, stSet, rfl, hD, hI, hR, rfl, rfl, h2.symm⟩

theorem setThreadCpuAffinityOnCore_of_admitted (st : SystemState)
    (vTargetTid : ValidThreadId) (affinity : Option CoreId) (executingCore : CoreId)
    (h : setAffinityAdmitted st vTargetTid.val affinity = true) :
    ∃ sgi, setThreadCpuAffinityOnCore st vTargetTid affinity executingCore =
      .ok (setAffinityPerform st vTargetTid.val affinity, sgi) := by
  unfold setAffinityAdmitted at h
  cases hT : st.getTcb? vTargetTid.val with
  | none => simp [hT] at h
  | some tcb =>
    simp only [hT, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hF, hD⟩, hI⟩, hR⟩ := h
    have hD' : (affinity.any (fun c => c.val ≥ st.machine.declaredCoreCount)) = false := by
      cases affinity <;> simp_all
    have hT0 : (vacateForAffinityChange st vTargetTid.val (determineTargetCore st vTargetTid.val)
        (affinity.getD bootCoreId)).getTcb? vTargetTid.val = some tcb := by
      rw [vacateForAffinityChange_getTcb?]; exact hT
    have hF0 : (vacateForAffinityChange st vTargetTid.val (determineTargetCore st vTargetTid.val)
        (affinity.getD bootCoreId)).objects.findsInPlace vTargetTid.val.toObjId = true := by
      rw [vacateForAffinityChange_objects]; exact hF
    unfold setThreadCpuAffinityOnCore setThreadCpuAffinityWithMigration setThreadCpuAffinity
    simp only [hT, hD', hI, hR, Bool.false_eq_true, ↓reduceIte,
      SystemState.getTcbWitnessed?_eq_some hT0]
    rw [SystemState.rewriteObject_tcb_eq_updateTcb hT0 (fun t => { t with cpuAffinity := affinity })]
    unfold setAffinityPerform
    simp only [hT]
    exact ⟨_, rfl⟩

end SeLe4n.Kernel
