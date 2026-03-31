/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- M-03/WS-E6: EDF (Earliest Deadline First) tie-breaking
-- ============================================================================

/-- M-03/WS-E6: Three-level scheduling comparison predicate.

Returns `true` when the incumbent candidate (`incTid`) should be replaced
by the challenger (`chalTid`). The three-level policy is:
1. **Priority:** higher numeric priority strictly wins.
2. **EDF:** at equal priority, earlier (lower nonzero) deadline wins.
   A nonzero deadline always beats a zero (no-deadline) challenger at
   equal priority.
3. **FIFO:** if both priority and deadline are equal (or both zero),
   the incumbent is retained (first-in-queue stability).

This mirrors seL4 MCS scheduling semantics where sporadic servers use
deadline-based selection within fixed-priority bands.

S5-I: Within equal priority levels, tie-breaking follows EDF (Earliest
Deadline First). When deadlines are also equal, the incumbent is retained
(line `cd < id` with strict less-than), implementing FIFO ordering among
equal-priority equal-deadline threads. This matches seL4's round-robin
behavior at each priority level. -/
def isBetterCandidate
    (incPrio : SeLe4n.Priority) (incDeadline : SeLe4n.Deadline)
    (chalPrio : SeLe4n.Priority) (chalDeadline : SeLe4n.Deadline) : Bool :=
  if chalPrio.toNat > incPrio.toNat then true
  else if chalPrio.toNat < incPrio.toNat then false
  else -- equal priority: EDF tie-breaking
    match chalDeadline.toNat, incDeadline.toNat with
    | 0, _ => false  -- challenger has no deadline: never beats incumbent
    | _, 0 => true   -- challenger has deadline, incumbent doesn't: challenger wins
    | cd, id => cd < id  -- both have deadlines: earlier wins; equal = FIFO (retain incumbent)

/-- M-03/WS-E6: FIFO stability — a candidate is never strictly better than itself. -/
theorem isBetterCandidate_irrefl (prio : SeLe4n.Priority) (dl : SeLe4n.Deadline) :
    isBetterCandidate prio dl prio dl = false := by
  unfold isBetterCandidate
  simp [show ¬(prio.toNat > prio.toNat) from by omega]
  cases h : dl.toNat with
  | zero => rfl
  | succ n => simp [Nat.lt_irrefl]

/-- M-03/WS-E6: Strict ordering — if A beats B, then B does not beat A. -/
theorem isBetterCandidate_asymm
    (p1 p2 : SeLe4n.Priority) (d1 d2 : SeLe4n.Deadline)
    (h : isBetterCandidate p1 d1 p2 d2 = true) :
    isBetterCandidate p2 d2 p1 d1 = false := by
  unfold isBetterCandidate at h ⊢
  -- Goal: does (p1 as challenger) beat (p2 as incumbent)? We need false.
  -- Hypothesis h: does (p2 as challenger) beat (p1 as incumbent)? Known true.
  -- Split on the goal's priority check: p1.toNat > p2.toNat?
  by_cases hGt : p1.toNat > p2.toNat
  · -- p1 > p2: then at h, since p2 is challenger and p1 is incumbent,
    -- p2.toNat > p1.toNat is false, and p2.toNat < p1.toNat is true → h says false=true
    have : ¬(p2.toNat > p1.toNat) := by omega
    simp [this, show p2.toNat < p1.toNat from by omega] at h
  · by_cases hLt : p1.toNat < p2.toNat
    · -- p1 < p2: goal reduces to false. Done!
      simp [show ¬(p1.toNat > p2.toNat) from hGt, hLt]
    · -- p1 = p2: equal priority, EDF tie-breaking
      have hEq : p1.toNat = p2.toNat := by omega
      -- In h: p2.toNat > p1.toNat is false, p2.toNat < p1.toNat is false → EDF
      simp [show ¬(p2.toNat > p1.toNat) from by omega,
            show ¬(p2.toNat < p1.toNat) from by omega] at h
      -- In goal: p1.toNat > p2.toNat is false, p1.toNat < p2.toNat is false → EDF
      simp [hGt, show ¬(p1.toNat < p2.toNat) from hLt]
      -- h and goal are now about deadline comparisons in opposite directions
      revert h
      cases hd2 : d2.toNat with
      | zero => simp
      | succ n =>
          cases hd1 : d1.toNat with
          | zero => simp
          | succ m => simp; omega

/-- WS-H6: transitivity for the strict candidate-preference relation. -/
theorem isBetterCandidate_transitive
    (p1 p2 p3 : SeLe4n.Priority) (d1 d2 d3 : SeLe4n.Deadline)
    (h12 : isBetterCandidate p1 d1 p2 d2 = true)
    (h23 : isBetterCandidate p2 d2 p3 d3 = true) :
    isBetterCandidate p1 d1 p3 d3 = true := by
  unfold isBetterCandidate at h12 h23 ⊢
  by_cases h31 : p3.toNat > p1.toNat
  · simp [h31]
  · have hLe31 : p3.toNat ≤ p1.toNat := Nat.le_of_not_gt h31
    by_cases h13 : p1.toNat < p3.toNat
    · omega
    · have hp12 : p2.toNat > p1.toNat ∨ p2.toNat = p1.toNat := by
        by_cases hp : p2.toNat > p1.toNat
        · exact Or.inl hp
        · have : p2.toNat = p1.toNat := by
            have hp' : ¬(p2.toNat < p1.toNat) := by
              intro hlt
              simp [Nat.not_lt.mpr (Nat.le_of_lt hlt), hlt] at h12
            omega
          exact Or.inr this
      have hp23 : p3.toNat > p2.toNat ∨ p3.toNat = p2.toNat := by
        by_cases hp : p3.toNat > p2.toNat
        · exact Or.inl hp
        · have : p3.toNat = p2.toNat := by
            have hp' : ¬(p3.toNat < p2.toNat) := by
              intro hlt
              simp [Nat.not_lt.mpr (Nat.le_of_lt hlt), hlt] at h23
            omega
          exact Or.inr this
      have hEqP : p1.toNat = p2.toNat ∧ p2.toNat = p3.toNat := by
        have hge12 : p2.toNat ≥ p1.toNat := by omega
        have hge23 : p3.toNat ≥ p2.toNat := by omega
        have hle13 : p3.toNat ≤ p1.toNat := hLe31
        omega
      rcases hEqP with ⟨hEq12, hEq23⟩
      simp [hEq12, hEq23] at h12 h23 ⊢
      revert h12 h23
      cases hd1 : d1.toNat <;> cases hd2 : d2.toNat <;> cases hd3 : d3.toNat <;> simp
      omega

/-- M-03/WS-E6: Three-level scheduling selection.

Folds over the runnable list accumulating the best candidate using the
three-level `isBetterCandidate` predicate. The accumulator carries
`(ThreadId × Priority × Deadline)` to avoid re-reading the object store. -/
def chooseBestRunnableBy
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :=
  match runnable with
  | [] => .ok best
  | tid :: rest =>
      match objects tid.toObjId with
      | some (.tcb tcb) =>
          let best' :=
            if eligible tcb then
              match best with
              | none => some (tid, tcb.priority, tcb.deadline)
              | some (_, bestPrio, bestDl) =>
                  if isBetterCandidate bestPrio bestDl tcb.priority tcb.deadline then
                    some (tid, tcb.priority, tcb.deadline)
                  else
                    best
            else
              best
          chooseBestRunnableBy objects eligible rest best'
      | _ => .error .schedulerInvariantViolation

def chooseBestRunnableInDomain
    (objects : SeLe4n.ObjId → Option KernelObject)
    (runnable : List SeLe4n.ThreadId)
    (activeDomain : SeLe4n.DomainId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :=
  chooseBestRunnableBy objects (fun tcb => tcb.domain == activeDomain) runnable best

/-- WS-G4/F-P07: Bucket-first scheduling selection.

Scans only the max-priority bucket for domain-eligible threads, reducing
best-candidate selection from O(t) to O(k) where k is the bucket size
(typically 1-3 in real systems). Falls back to full-list scan if the
max-priority bucket contains no eligible thread (e.g., all max-priority
threads are in a different domain). -/
def chooseBestInBucket
    (objects : SeLe4n.ObjId → Option KernelObject)
    (rq : RunQueue)
    (activeDomain : SeLe4n.DomainId) :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :=
  let maxBucket := rq.maxPriorityBucket
  match chooseBestRunnableInDomain objects maxBucket activeDomain none with
  | .error e => .error e
  | .ok (some result) => .ok (some result)
  | .ok none =>
    -- Max-priority bucket had no eligible thread in this domain;
    -- fall back to full-list scan.
    chooseBestRunnableInDomain objects rq.toList activeDomain none

/-- WS-H6: bucket-first candidate selection is definitionally equivalent
to "scan max bucket then fallback to full scan" semantics. -/
theorem bucketFirst_fullScan_equivalence
    (objects : SeLe4n.ObjId → Option KernelObject)
    (rq : RunQueue)
    (activeDomain : SeLe4n.DomainId) :
    chooseBestInBucket objects rq activeDomain =
      (match chooseBestRunnableInDomain objects rq.maxPriorityBucket activeDomain none with
       | .error e => .error e
       | .ok (some result) => .ok (some result)
       | .ok none => chooseBestRunnableInDomain objects rq.toList activeDomain none) := by
  rfl

-- ============================================================================
-- Z4-B: Effective scheduling parameter resolution
-- ============================================================================

/-- Z4-B: Resolve effective scheduling parameters for a thread.

If the thread is bound to a SchedContext (`.bound scId` or `.donated scId _`),
returns the SchedContext's `(priority, deadline, domain)`. Otherwise falls back
to the TCB's legacy fields. Returns `none` only if the SchedContext object is
missing from the store (a consistency violation).

This is the central resolution point used by all scheduler operations to
determine a thread's scheduling parameters, enabling the migration from
monolithic TCB fields to first-class SchedContext objects. -/
def effectivePriority (st : SystemState) (tcb : TCB)
    : Option (SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :=
  match tcb.schedContextBinding with
  | .unbound => some (tcb.priority, tcb.deadline, tcb.domain)
  | .bound scId | .donated scId _ =>
    match st.objects[scId.toObjId]? with
    | some (.schedContext sc) => some (sc.priority, sc.deadline, sc.domain)
    | _ => none

/-- Z4-B: For unbound threads, `effectivePriority` always returns the TCB fields. -/
theorem effectivePriority_unbound (st : SystemState) (tcb : TCB)
    (h : tcb.schedContextBinding = .unbound) :
    effectivePriority st tcb = some (tcb.priority, tcb.deadline, tcb.domain) := by
  simp [effectivePriority, h]

-- ============================================================================
-- Z4-C: Budget eligibility predicate
-- ============================================================================

/-- Z4-C: Check whether a thread has sufficient CBS budget to be scheduled.

For unbound threads (legacy mode), returns `true` — they use the existing
`timeSlice` mechanism and are always budget-eligible. For SchedContext-bound
threads, returns `true` only if `budgetRemaining > 0`. Returns `true` for
missing SchedContext objects (fail-open for robustness; the binding consistency
invariant ensures this is unreachable under normal operation). -/
def hasSufficientBudget (st : SystemState) (tcb : TCB) : Bool :=
  match tcb.schedContextBinding with
  | .unbound => true
  | .bound scId | .donated scId _ =>
    match st.objects[scId.toObjId]? with
    | some (.schedContext sc) => sc.budgetRemaining.isPositive
    | _ => true

/-- Z4-C: Unbound threads always have sufficient budget. -/
theorem hasSufficientBudget_unbound (st : SystemState) (tcb : TCB)
    (h : tcb.schedContextBinding = .unbound) :
    hasSufficientBudget st tcb = true := by
  simp [hasSufficientBudget, h]

-- ============================================================================
-- Z4-D/E: SchedContext-aware scheduling selection
-- ============================================================================

/-- Z4-D/E: Resolve effective priority and deadline for a TCB.

Returns the priority/deadline pair to use for scheduling comparison.
For bound threads, uses SchedContext parameters; for unbound threads,
falls back to TCB legacy fields. -/
@[inline] def resolveEffectivePrioDeadline (st : SystemState) (tcb : TCB)
    : SeLe4n.Priority × SeLe4n.Deadline :=
  match tcb.schedContextBinding with
  | .unbound => (tcb.priority, tcb.deadline)
  | .bound scId | .donated scId _ =>
    match st.objects[scId.toObjId]? with
    | some (.schedContext sc) => (sc.priority, sc.deadline)
    | _ => (tcb.priority, tcb.deadline)

/-- Z4-D/E: SchedContext-aware three-level scheduling selection.

Extends `chooseBestRunnableBy` with two SchedContext enhancements:
1. **Budget eligibility** (Z4-D): Threads with exhausted SchedContext budgets
   are excluded via the composed `eligible` predicate.
2. **Effective priority** (Z4-E): Priority and deadline are resolved from the
   SchedContext when bound, falling back to TCB fields when unbound.

The three-level comparison logic (`isBetterCandidate`) is unchanged — only
the priority/deadline source and eligibility filter differ. -/
def chooseBestRunnableEffective
    (st : SystemState)
    (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :=
  match runnable with
  | [] => .ok best
  | tid :: rest =>
      match st.objects.get? tid.toObjId with
      | some (.tcb tcb) =>
          let best' :=
            if eligible tcb && hasSufficientBudget st tcb then
              let (prio, dl) := resolveEffectivePrioDeadline st tcb
              match best with
              | none => some (tid, prio, dl)
              | some (_, bestPrio, bestDl) =>
                  if isBetterCandidate bestPrio bestDl prio dl then
                    some (tid, prio, dl)
                  else
                    best
            else
              best
          chooseBestRunnableEffective st eligible rest best'
      | _ => .error .schedulerInvariantViolation

/-- Z4-D/E: SchedContext-aware domain-filtered selection. -/
def chooseBestRunnableInDomainEffective
    (st : SystemState)
    (runnable : List SeLe4n.ThreadId)
    (activeDomain : SeLe4n.DomainId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :=
  chooseBestRunnableEffective st (fun tcb => tcb.domain == activeDomain) runnable best

/-- Z4-D/E: SchedContext-aware bucket-first selection.

Uses the effective selection variant for both the max-priority bucket scan
and the full-list fallback. -/
def chooseBestInBucketEffective
    (st : SystemState)
    (rq : RunQueue)
    (activeDomain : SeLe4n.DomainId) :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :=
  let maxBucket := rq.maxPriorityBucket
  match chooseBestRunnableInDomainEffective st maxBucket activeDomain none with
  | .error e => .error e
  | .ok (some result) => .ok (some result)
  | .ok none =>
    chooseBestRunnableInDomainEffective st rq.toList activeDomain none

/-- M-03/M-05 WS-E6/WS-G4: Choose the highest-priority runnable thread from the
active domain using deterministic selection: priority > EDF deadline > FIFO.

WS-G4/F-P07: Uses bucket-first strategy — scans only the max-priority bucket
first (O(k) where k is bucket size), falling back to full-list scan only if
the max-priority bucket has no eligible thread in the active domain.

S5-I: FIFO tie-breaking semantics — within a priority level, `List.head?` on
the filtered candidate list selects the first thread inserted (FIFO order).
When multiple threads share the same priority and EDF deadline,
`isBetterCandidate` retains the incumbent (`cd < id` with strict less-than),
so the earliest-queued thread wins. This matches seL4's round-robin behavior
at each fixed-priority band.

This is a pure read operation — the system state is returned unchanged.
If no runnable thread exists in the active domain, selection returns `none`. -/
def chooseThread : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    match chooseBestInBucket st.objects.get? st.scheduler.runQueue st.scheduler.activeDomain with
    | .error e => .error e
    | .ok none => .ok (none, st)
    | .ok (some (tid, _, _)) => .ok (some tid, st)

/-- Z4-D/E: SchedContext-aware thread selection.

Uses `chooseBestInBucketEffective` which filters by budget eligibility and
resolves effective priorities from SchedContext objects. This is used by the
extended scheduler operations (`scheduleEffective`, `timerTickWithBudget`,
`handleYieldWithBudget`). The original `chooseThread` is preserved for
backward compatibility with existing preservation proofs. -/
def chooseThreadEffective : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    match chooseBestInBucketEffective st st.scheduler.runQueue st.scheduler.activeDomain with
    | .error e => .error e
    | .ok none => .ok (none, st)
    | .ok (some (tid, _, _)) => .ok (some tid, st)

/-- Z4-D/E: `chooseThreadEffective` is read-only — preserves state. -/
theorem chooseThreadEffective_preserves_state
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hStep : chooseThreadEffective st = .ok (next, st')) :
    st' = st := by
  unfold chooseThreadEffective at hStep
  cases hPick : chooseBestInBucketEffective st st.scheduler.runQueue st.scheduler.activeDomain with
  | error e => simp [hPick] at hStep
  | ok best =>
      cases best with
      | none =>
          rcases (by simpa [hPick] using hStep : none = next ∧ st = st') with ⟨_, hSt⟩
          simpa using hSt.symm
      | some triple =>
          obtain ⟨tid, prio, dl⟩ := triple
          rcases (by simpa [hPick] using hStep : some tid = next ∧ st = st') with ⟨_, hSt⟩
          simpa using hSt.symm

/-- WS-H12c/H-03/V5-D: Save the outgoing (current) thread's machine registers into
its TCB `registerContext` field. If no thread is current, returns the state
unchanged. This is an internal helper used inline by `schedule`.

V5-D (M-DEF-4): When `current = some tid` but the TCB lookup fails (non-TCB
object or missing ObjId), the state is returned unchanged — the save is silently
dropped. Under `currentThreadValid` (part of `schedulerInvariantBundle`), this
branch is unreachable: the invariant guarantees the current thread resolves to
a valid TCB. The `saveOutgoingContextChecked` variant below provides an explicit
success indicator for callers that need to detect this (unreachable) failure. -/
def saveOutgoingContext (st : SystemState) : SystemState :=
  match st.scheduler.current with
  | none => st
  | some outTid =>
      match st.objects[outTid.toObjId]? with
      | some (.tcb outTcb) =>
          let obj := KernelObject.tcb { outTcb with registerContext := st.machine.regs }
          { st with objects := st.objects.insert outTid.toObjId obj }
      | _ => st

/-- V5-D (M-DEF-4): Checked variant of `saveOutgoingContext` that returns a
    success indicator. Returns `(state, true)` on successful save (or no current
    thread), `(state, false)` when the current thread's TCB lookup fails.

    Under `currentThreadValid`, the `false` branch is unreachable. This variant
    exists for defense-in-depth: callers at API boundaries can assert on the
    success flag to surface invariant violations early. -/
def saveOutgoingContextChecked (st : SystemState) : SystemState × Bool :=
  match st.scheduler.current with
  | none => (st, true)
  | some outTid =>
      match st.objects[outTid.toObjId]? with
      | some (.tcb outTcb) =>
          let obj := KernelObject.tcb { outTcb with registerContext := st.machine.regs }
          ({ st with objects := st.objects.insert outTid.toObjId obj }, true)
      | _ => (st, false)

/-- V5-D: The checked variant agrees with the unchecked variant on the state component. -/
theorem saveOutgoingContextChecked_fst_eq (st : SystemState) :
    (saveOutgoingContextChecked st).1 = saveOutgoingContext st := by
  unfold saveOutgoingContextChecked saveOutgoingContext
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases h : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some obj =>
          cases obj <;> simp_all

/-- WS-H12c/H-03/V5-E: Restore the incoming thread's register context into the
machine register file. If the incoming TCB is not found, returns the state
unchanged (unreachable under `currentThreadValid`).

V5-E (M-DEF-5): When the TCB lookup fails, the restore is silently skipped.
Under `currentThreadValid`, this branch is unreachable. The checked variant
`restoreIncomingContextChecked` provides an explicit success indicator. -/
def restoreIncomingContext (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.objects[tid.toObjId]? with
  | some (.tcb inTcb) =>
      { st with machine := { st.machine with regs := inTcb.registerContext } }
  | _ => st

/-- V5-E (M-DEF-5): Checked variant of `restoreIncomingContext` that returns a
    success indicator. Returns `(state, true)` on successful restore,
    `(state, false)` when the thread's TCB lookup fails.

    Under `currentThreadValid`, the `false` branch is unreachable. -/
def restoreIncomingContextChecked (st : SystemState)
    (tid : SeLe4n.ThreadId) : SystemState × Bool :=
  match st.objects[tid.toObjId]? with
  | some (.tcb inTcb) =>
      ({ st with machine := { st.machine with regs := inTcb.registerContext } }, true)
  | _ => (st, false)

/-- V5-E: The checked variant agrees with the unchecked variant on the state component. -/
theorem restoreIncomingContextChecked_fst_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (restoreIncomingContextChecked st tid).1 = restoreIncomingContext st tid := by
  unfold restoreIncomingContextChecked restoreIncomingContext
  cases h : st.objects[tid.toObjId]? with
  | none => simp_all
  | some obj =>
      cases obj <;> simp_all

/-- Z4-D/E: For a system with all unbound threads, the effective selection
reduces to the original selection. -/
theorem chooseBestRunnableEffective_unbound_equiv
    (st : SystemState)
    (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (hAllUnbound : ∀ tid ∈ runnable, ∀ tcb : TCB,
      st.objects.get? tid.toObjId = some (.tcb tcb) →
      tcb.schedContextBinding = .unbound) :
    chooseBestRunnableEffective st eligible runnable best =
    chooseBestRunnableBy st.objects.get? eligible runnable best := by
  induction runnable generalizing best with
  | nil => simp [chooseBestRunnableEffective, chooseBestRunnableBy]
  | cons tid rest ih =>
    simp only [chooseBestRunnableEffective, chooseBestRunnableBy]
    cases hObj : st.objects.get? tid.toObjId with
    | none => rfl
    | some obj =>
      cases obj with
      | tcb tcb =>
        have hMem : tid ∈ tid :: rest := List.mem_cons_self ..
        have hUnb := hAllUnbound tid hMem tcb hObj
        simp [hasSufficientBudget_unbound st tcb hUnb, Bool.and_true,
              resolveEffectivePrioDeadline, hUnb]
        apply ih
        intro t hMemRest
        exact hAllUnbound t (List.mem_cons_of_mem _ hMemRest)
      | _ => rfl

