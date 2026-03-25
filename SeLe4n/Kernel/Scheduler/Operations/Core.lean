/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Selection

namespace SeLe4n.Kernel

open SeLe4n.Model

-- WS-H12c: Frame lemmas — context save/restore do not affect scheduler state.

@[simp] theorem saveOutgoingContext_scheduler (st : SystemState) :
    (saveOutgoingContext st).scheduler = st.scheduler := by
  simp only [saveOutgoingContext]
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases h : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some obj =>
          revert h
          cases obj <;> intro h <;> simp_all

@[simp] theorem restoreIncomingContext_scheduler (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).scheduler = st.scheduler := by
  simp only [restoreIncomingContext]
  cases h : st.objects[tid.toObjId]? with
  | none => simp_all
  | some obj =>
      revert h
      cases obj <;> intro h <;> simp_all

@[simp] theorem restoreIncomingContext_objects (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).objects = st.objects := by
  simp only [restoreIncomingContext]
  cases h : st.objects[tid.toObjId]? with
  | none => simp_all
  | some obj =>
      revert h
      cases obj <;> intro h <;> simp_all

/-- `saveOutgoingContext` preserves the existence of a TCB at any object ID.
If `st.objects[oid]? = some (.tcb tcb)`, then there exists a TCB at `oid`
in `(saveOutgoingContext st).objects` as well. -/
theorem saveOutgoingContext_preserves_tcb
    (st : SystemState) (oid : SeLe4n.ObjId) (tcb : TCB)
    (h : st.objects[oid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt) :
    ∃ tcb', (saveOutgoingContext st).objects[oid]? = some (.tcb tcb') := by
  unfold saveOutgoingContext
  cases hCur : st.scheduler.current with
  | none => exact ⟨tcb, h⟩
  | some outTid =>
      dsimp only
      cases hOut : st.objects[outTid.toObjId]? with
      | none => exact ⟨tcb, h⟩
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              dsimp only
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              by_cases hEq : outTid.toObjId == oid
              · simp [hEq]
              · simp [hEq]; exact ⟨tcb, h⟩
          | endpoint _ => exact ⟨tcb, h⟩
          | notification _ => exact ⟨tcb, h⟩
          | cnode _ => exact ⟨tcb, h⟩
          | vspaceRoot _ => exact ⟨tcb, h⟩
          | untyped _ => exact ⟨tcb, h⟩

/-- `saveOutgoingContext` preserves all TCB fields except `registerContext`. -/
theorem saveOutgoingContext_tcb_fields
    (st : SystemState) (oid : SeLe4n.ObjId) (tcb : TCB)
    (h : st.objects[oid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt) :
    ∃ tcb', (saveOutgoingContext st).objects[oid]? = some (.tcb tcb') ∧
      tcb'.domain = tcb.domain ∧
      tcb'.priority = tcb.priority ∧
      tcb'.deadline = tcb.deadline ∧
      tcb'.timeSlice = tcb.timeSlice := by
  unfold saveOutgoingContext
  cases hCur : st.scheduler.current with
  | none => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
  | some outTid =>
      dsimp only
      cases hOut : st.objects[outTid.toObjId]? with
      | none => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              dsimp only
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              by_cases hEq : outTid.toObjId == oid
              · simp only [hEq, ite_true]
                have hEq' := beq_iff_eq.mp hEq
                subst hEq'
                rw [hOut] at h; cases h
                exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
              · simp [hEq]; exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
          | endpoint _ => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
          | notification _ => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
          | cnode _ => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
          | vspaceRoot _ => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩
          | untyped _ => exact ⟨tcb, h, rfl, rfl, rfl, rfl⟩

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
  cases hCur : st.scheduler.current with
  | none => rfl
  | some outTid =>
      dsimp only
      cases hOut : st.objects[outTid.toObjId]? with
      | none => rfl
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              dsimp only
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              have hNe : ¬(outTid.toObjId == oid) := by
                intro hEq
                have hEq' := beq_iff_eq.mp hEq
                subst hEq'; exact hNonTcb outTcb hOut
              simp [hNe]
          | endpoint _ => rfl
          | notification _ => rfl
          | cnode _ => rfl
          | vspaceRoot _ => rfl
          | untyped _ => rfl

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
  cases hCur : st.scheduler.current with
  | none => exact hOrig
  | some outTid =>
      dsimp only
      cases hOut : st.objects[outTid.toObjId]? with
      | none => exact hOrig
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              dsimp only
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              by_cases hEq : outTid.toObjId == tid.toObjId
              · -- Same key: inserted TCB has same timeSlice as original
                simp [hEq]
                have hEq' := beq_iff_eq.mp hEq
                rw [hEq'] at hOut; simp [hOut] at hOrig; exact hOrig
              · simp [hEq]; exact hOrig
          | endpoint _ => exact hOrig
          | notification _ => exact hOrig
          | cnode _ => exact hOrig
          | vspaceRoot _ => exact hOrig
          | untyped _ => exact hOrig

/-- `saveOutgoingContext` preserves `objects.invExt`. The context save
inserts a TCB at an existing key, which preserves the Robin Hood invariant. -/
theorem saveOutgoingContext_preserves_objects_invExt
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (saveOutgoingContext st).objects.invExt := by
  unfold saveOutgoingContext
  cases hCur : st.scheduler.current with
  | none => exact hObjInv
  | some outTid =>
      dsimp only
      cases hObj : st.objects[outTid.toObjId]? with
      | none => simp; exact hObjInv
      | some obj =>
          cases obj with
          | tcb outTcb =>
              dsimp only
              exact RHTable_insert_preserves_invExt st.objects _ _ hObjInv
          | _ => simp; exact hObjInv

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
  simp only [restoreIncomingContext, hTcb]

/-- WS-H12c: `restoreIncomingContext` does not change the machine state when
the given thread ID does not correspond to a TCB in the object store. -/
@[simp] theorem restoreIncomingContext_machine_no_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (h : ∀ tcb, st.objects[tid.toObjId]? ≠ some (.tcb tcb)) :
    (restoreIncomingContext st tid).machine = st.machine := by
  unfold restoreIncomingContext
  cases hObj : st.objects[tid.toObjId]? with
  | none => rfl
  | some obj =>
      cases obj with
      | tcb t => exact absurd hObj (h t)
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => rfl

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
`tid ∈ st'.scheduler.runQueue`.

**U8-D/U-L26: Starvation and fairness:** This is a strict fixed-priority
preemptive scheduler matching seL4's classic scheduling model. Starvation
freedom is NOT a property of this scheduler — a continuously runnable
high-priority thread will indefinitely preempt lower-priority threads.
seL4 delegates starvation prevention to user-level policy (e.g., MCS
scheduling extensions, which are not yet modeled in seLe4n). -/
def schedule : Kernel Unit :=
  fun st =>
    match chooseThread st with
    | .error e => .error e
    | .ok (none, st') =>
        -- WS-H12c: save outgoing context before going idle
        let stSaved := saveOutgoingContext st'
        setCurrentThread none stSaved
    | .ok (some tid, st') =>
        match st'.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            if tid ∈ st'.scheduler.runQueue ∧ tcb.domain = st'.scheduler.activeDomain then
              -- WS-H12c: save outgoing thread's register context
              let stSaved := saveOutgoingContext st'
              -- WS-H12b: dequeue before dispatch (seL4 tcbSchedDequeue)
              let stDequeued := { stSaved with scheduler := { stSaved.scheduler with
                  runQueue := stSaved.scheduler.runQueue.remove tid } }
              -- WS-H12c: restore incoming thread's register context
              let stRestored := restoreIncomingContext stDequeued tid
              setCurrentThread (some tid) stRestored
            else
              .error .schedulerInvariantViolation
        | _ => .error .schedulerInvariantViolation

/-- WS-H12b/H-04 + WS-H12c/H-03: Yield semantics with dequeue-on-dispatch.

Under dequeue-on-dispatch, the current thread is NOT in the run queue.
Yield re-enqueues the current thread at the back of its priority bucket
(insert + rotateToBack), then calls schedule to select a new thread.

Context save/restore is handled inline by `schedule`: the outgoing thread's
registers are saved to its TCB and the incoming thread's registers are
restored from its TCB, establishing `contextMatchesCurrent` atomically.

This mirrors seL4's `handleYield` → `tcbSchedDequeue` + `tcbSchedAppend`
(append = enqueue at tail) → `rescheduleRequired` → `schedule()`. -/
def handleYield : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none => schedule st
    | some tid =>
        match st.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            -- WS-H12b: re-enqueue at back of priority bucket, then schedule
            let rq' := (st.scheduler.runQueue.insert tid tcb.priority).rotateToBack tid
            let st' := { st with scheduler := { st.scheduler with runQueue := rq' } }
            schedule st'
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- M-04/WS-E6: Time-slice preemption
-- ============================================================================

/-- M-04/WS-E6: Default time-slice quantum (ticks per scheduling round).
Factored into a named constant so the reset value in `timerTick` stays
synchronized with `TCB.timeSlice` default. -/
def defaultTimeSlice : Nat := 5

/-- WS-H12b/H-04 + WS-H12c/H-03: Handle a timer tick with dequeue-on-dispatch
and inline context switch semantics.

Behavior:
1. If no thread is current, advance the machine timer only.
2. If the current thread's time-slice has not expired (> 1 after decrement),
   decrement and advance the machine timer.
3. If the time-slice expires (≤ 1), reset it to `defaultTimeSlice`,
   re-enqueue the current thread into the run queue, and reschedule.

Under dequeue-on-dispatch, the current thread is NOT in the run queue.
On preemption, we insert it back (seL4's `tcbSchedEnqueue(current)`)
before calling `schedule()`. Context save/restore is handled inline by
`schedule`: the outgoing thread's registers are saved to its TCB and
the incoming thread's registers are restored, establishing
`contextMatchesCurrent` atomically. -/
def timerTick : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none =>
        -- No current thread: just advance the timer
        .ok ((), { st with machine := tick st.machine })
    | some tid =>
        match st.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            if tcb.timeSlice ≤ 1 then
              -- Time-slice expired: reset, re-enqueue, reschedule
              let tcb' := { tcb with timeSlice := defaultTimeSlice }
              let st' := { st with objects := st.objects.insert tid.toObjId (.tcb tcb'), machine := tick st.machine }
              -- WS-H12b: re-enqueue current thread before schedule
              let st'' := { st' with scheduler := { st'.scheduler with
                  runQueue := st'.scheduler.runQueue.insert tid tcb.priority } }
              schedule st''
            else
              -- Time-slice not expired: decrement and continue
              let tcb' := { tcb with timeSlice := tcb.timeSlice - 1 }
              .ok ((), { st with objects := st.objects.insert tid.toObjId (.tcb tcb'), machine := tick st.machine })
        | _ => .error .schedulerInvariantViolation

-- ============================================================================
-- M-05/WS-E6: Domain scheduling
-- ============================================================================

/-- M-05/WS-E6: Compatibility alias for domain-aware scheduling selection.

`chooseThread` is now domain-aware; this entry point remains for call sites that
expect explicit domain-oriented naming. -/
def chooseThreadInDomain : Kernel (Option SeLe4n.ThreadId) :=
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
runnable pool for its next domain slot. -/
def switchDomain : Kernel Unit :=
  fun st =>
    let schedule := st.scheduler.domainSchedule
    match schedule with
    | [] => .ok ((), st)  -- single-domain mode: no-op
    | _ =>
        let nextIdx := (st.scheduler.domainScheduleIndex + 1) % schedule.length
        match schedule[nextIdx]? with
        | none => .ok ((), st)  -- safety: should not happen with valid modular index
        | some entry =>
            -- U-M39: Save outgoing context before clearing current
            let stSaved := saveOutgoingContext st
            -- WS-H12b: re-enqueue current thread before domain switch
            -- All reads use st (not stSaved) to keep scheduler computation identical
            let rq' := match st.scheduler.current with
              | none => st.scheduler.runQueue
              | some tid =>
                  match st.objects[tid.toObjId]? with
                  | some (.tcb tcb) => st.scheduler.runQueue.insert tid tcb.priority
                  | _ => st.scheduler.runQueue
            let sched' := { st.scheduler with
              runQueue := rq'
              current := none
              activeDomain := DomainScheduleEntry.domain entry
              domainTimeRemaining := DomainScheduleEntry.length entry
              domainScheduleIndex := nextIdx
            }
            .ok ((), { stSaved with scheduler := sched' })

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
      · obtain ⟨_, rfl⟩ := hStep; exact hObjInv
      · simp at hStep; obtain ⟨_, rfl⟩ := hStep; dsimp
        exact saveOutgoingContext_preserves_objects_invExt st hObjInv

/-- M-05/WS-E6: Handle a domain tick. Decrements the domain time remaining;
if expired, switches to the next domain and reschedules. -/
def scheduleDomain : Kernel Unit :=
  fun st =>
    if st.scheduler.domainTimeRemaining ≤ 1 then
      match switchDomain st with
      | .error e => .error e
      | .ok ((), st') => schedule st'
    else
      let sched' := { st.scheduler with
        domainTimeRemaining := st.scheduler.domainTimeRemaining - 1
      }
      .ok ((), { st with scheduler := sched' })
