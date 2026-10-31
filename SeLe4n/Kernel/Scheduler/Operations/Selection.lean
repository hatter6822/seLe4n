-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.Concurrency.Sgi
import SeLe4n.Kernel.Scheduler.IdleThread
import SeLe4n.Kernel.Scheduler.RunQueueLinkFrame


namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId CoreId SgiKind)

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
    · have hSecondAtLeastFirst : p2.toNat > p1.toNat ∨ p2.toNat = p1.toNat := by
        by_cases hp : p2.toNat > p1.toNat
        · exact Or.inl hp
        · have : p2.toNat = p1.toNat := by
            have hp' : ¬(p2.toNat < p1.toNat) := by
              intro hlt
              simp [Nat.not_lt.mpr (Nat.le_of_lt hlt), hlt] at h12
            omega
          exact Or.inr this
      have hThirdAtLeastSecond : p3.toNat > p2.toNat ∨ p3.toNat = p2.toNat := by
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
`(ThreadId × Priority × Deadline)` to avoid re-reading the object store.

AF-49: FIFO tie-breaking is implicit in list order — `isBetterCandidate`
uses strict less-than (`cd < id`), so equal-priority equal-deadline
challengers never displace the incumbent. Since `RunQueue.insert` appends
to tail and the flat list preserves insertion order, the first-enqueued
thread at a given (priority, deadline) is naturally selected first. -/
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
      -- WS-SM SM8.B (PR #861 review round 15): **skip** an entry whose object is
      -- not a TCB rather than failing the scan.
      --
      -- This arm used to return `.error .schedulerInvariantViolation`, which
      -- made the *whole* selection fail — both the max-bucket scan and the
      -- full-list fallback — for every future call, because nothing on the
      -- failure path removes the offending entry.  One stale entry therefore
      -- wedged a core permanently, and the retype destroy path could produce one
      -- (it swept only the boot core; see `removeRunnableFromAllCores`).
      --
      -- The invariant that no such entry exists is unchanged and still carried:
      -- `runnableThreadsAreTCBs` (`Scheduler/Invariant.lean`) and its per-core
      -- form.  What changes is that the scheduler's *liveness* no longer depends
      -- on it — a violation now costs one unschedulable thread instead of one
      -- dead core.  Skipping is also the only safe direction: the entry cannot
      -- be dispatched, since there is no TCB to switch to.
      | _ => chooseBestRunnableBy objects eligible rest best

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
-- Z4-B / WS-RC R5.C.1: Effective scheduling parameter resolution
-- ============================================================================
--
-- WS-RC R5.C.1 (DEEP-SCH-02) full deprecation: The pre-R5 partial
-- `effectivePriority` helper (returning `Option (Priority × Deadline ×
-- DomainId)` and its three helper theorems
-- (`effectivePriority_unbound`, `effectivePriority_ge_pipBoost`,
-- `effectivePriority_noPip`) plus the bridge theorem
-- (`effectivePriority_some_eq_effectiveSchedParams`) are RETIRED.  All
-- callers now route through the total `effectiveSchedParams` helper
-- (defined below in the R5.C section), which falls back to TCB fields on
-- SC-lookup failure (matching `resolveEffectivePrioDeadline`'s
-- discipline).  Under `schedContextStoreConsistent` (part of
-- `crossSubsystemInvariant`), the SC-missing path is unreachable in
-- production, so the migration is semantics-preserving.
--
-- ============================================================================
-- Z4-C: Budget eligibility predicate
-- ============================================================================

/-- Z4-C: Check whether a thread has sufficient CBS budget to be scheduled.

For unbound threads (legacy mode), returns `true` — they use the existing
`timeSlice` mechanism and are always budget-eligible. For SchedContext-bound
threads, returns `true` only if `budgetRemaining > 0`.

Fail-closed: missing SchedContext → insufficient budget (defense-in-depth;
unreachable under `schedContextStoreConsistent` invariant). -/
def hasSufficientBudget (st : SystemState) (tcb : TCB) : Bool :=
  match tcb.schedContextBinding with
  | .unbound => true
  | .bound scId | .donated scId _ =>
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
    match st.getSchedContext? scId with
    | some sc => sc.budgetRemaining.isPositive
    | none    => false

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
falls back to TCB legacy fields.

**AF1-G: Fallback rationale** — The fallback to `tcb.priority`/`tcb.deadline`
when SchedContext lookup fails is safe because:
(1) Unbound threads trivially pass budget checks (`hasSufficientBudget` = true).
(2) Bound threads with a missing SchedContext are rejected by
    `schedContextStoreConsistent` (part of `crossSubsystemInvariant`), so the
    fallback path is unreachable under invariants.
(3) Domain check in `schedule` (Core.lean) uses static `tcb.domain`, which for
    a `.bound` thread agrees with `sc.domain` under `boundThreadDomainConsistent`
    (AE3-A) and for a `.donated` one is simply the donee's own — see the WS-OD
    note below.

**WS-OD (v0.35.3) — the donee's priority is its own.**  The `.donated` arm
takes the donor's *deadline* and the thread's **own** base priority, which is
`SystemState.threadBasePriority`'s classification
(`resolveEffectivePrioDeadline_fst_eq_threadBasePriority` is the pin).  A
donation moves a reservation, and a reservation carries budget, period and
deadline — not the right to be scheduled at the donor's band.  Reading
`sc.priority` here made a passive server inherit its client's priority for the
duration of the call *and*, through `updatePrioritySource`, let a
`.tcbSetPriority` on that server rewrite the client's reservation. -/
@[inline] def resolveEffectivePrioDeadline (st : SystemState) (tcb : TCB)
    : SeLe4n.Priority × SeLe4n.Deadline :=
  let (basePrio, dl) := match tcb.schedContextBinding with
    | .unbound => (tcb.priority, tcb.deadline)
    | .bound scId =>
      -- WS-RR (`v0.35.133`): the donor's deadline, the thread's OWN priority --
      -- the same shape as the `.donated` arm below, because since the one-home
      -- collapse `TCB.priority` is the only place a base priority is stored.
      -- Reading `sc.priority` here was the second half of the `v0.35.98`
      -- defect: the run queue is keyed by `TCB.boostedPriority`, so a state
      -- whose two homes had drifted scheduled the thread at one band and
      -- re-inserted it at the other.
      match st.getSchedContext? scId with
      | some sc => (tcb.priority, sc.deadline)
      | none    => (tcb.priority, tcb.deadline)
    | .donated scId _ =>
      -- WS-OD (v0.35.3): the donor's deadline, the donee's own priority.
      match st.getSchedContext? scId with
      | some sc => (tcb.priority, sc.deadline)
      | none    => (tcb.priority, tcb.deadline)
  -- D4-B: Apply PIP boost -- `Priority.raisedBy` (`Prelude.lean`), the one
  -- reading of "a base raised by an inherited boost", shared with
  -- `effectiveSchedParams` below and with the frozen run queue's mirror.
  (basePrio.raisedBy tcb.pipBoost, dl)

/-- WS-RR (`v0.35.133`): the base-priority half of the selector's resolution
**is** `TCB.boostedPriority` — the bucket key `schedulerPriorityMatch` records —
at every binding and with **no hypothesis**.

This is the bridge that lets the run-queue inserts (`resolveInsertPriority`,
used by `updatePipBoostOnCore` and the bound budget re-enqueue) preserve
`schedulerPriorityMatchOnCore`, and it is what makes a TCB-field comparison of
*priorities* sound wherever the selector's own ordering is the subject.

**It replaces three theorems whose hypotheses this cut killed**, and the
hypotheses are the point rather than the count.  `boostedPriority_eq_resolve_unbound`
(AI3-A) held at `.unbound`; `resolveEffectivePrioDeadline_fst_eq_boostedPriority_of_agree`
(SM5.I) extended it to `.bound` **under the `boundThreadPriorityConsistent`
agreement specialised to the thread**; `resolveEffectivePrioDeadline_fst_of_donated`
(WS-OD) was the `.donated` payoff.  With `TCB.priority` the base's one home the
`.bound` arm reads that field like the other two, so the agreement hypothesis is
discharged by nothing at all — and a reader who kept the `_of_agree` name would go
on believing that weakening the bind/configure propagation costs the selector its
priority ordering.  It does not: what that propagation is for is the configure
semantics and `boundThreadPriorityConsistent`, stated at `schedContextBind`.

**Deadlines have no counterpart and must not be read as having one** — see the
`chooseThreadEffectiveOnCore` gate below: bind copies only the priority, so a
TCB-*deadline* comparison still diverges from the selector for exactly the bound
threads CBS exists for. -/
theorem resolveEffectivePrioDeadline_fst_eq_boostedPriority
    (st : SystemState) (tcb : TCB) :
    (resolveEffectivePrioDeadline st tcb).1 = tcb.boostedPriority := by
  cases hb : tcb.schedContextBinding with
  | unbound =>
    cases hboost : tcb.pipBoost <;>
      simp [resolveEffectivePrioDeadline, TCB.boostedPriority, hb, hboost]
  | bound scId =>
    cases hsc : st.getSchedContext? scId <;>
      cases hboost : tcb.pipBoost <;>
        simp [resolveEffectivePrioDeadline, TCB.boostedPriority, hb, hsc, hboost]
  | donated scId owner =>
    cases hsc : st.getSchedContext? scId <;>
      cases hboost : tcb.pipBoost <;>
        simp [resolveEffectivePrioDeadline, TCB.boostedPriority, hb, hsc, hboost]

/-- WS-OD (v0.35.3): the base-priority half of `resolveEffectivePrioDeadline`
**is** `SystemState.threadBasePriority`, unconditionally.  This is the pin that
`Selection.lean`'s resolver and `Model/State.lean`'s canonical answer to "what
priority does this thread run at" cannot diverge: a site that classified
`.donated` the other way would fail to elaborate here. -/
theorem resolveEffectivePrioDeadline_fst_eq_threadBasePriority
    (st : SystemState) (tcb : TCB) :
    (resolveEffectivePrioDeadline st tcb).1 =
      (match tcb.pipBoost with
       | none => st.threadBasePriority tcb
       | some boostPrio => ⟨Nat.max (st.threadBasePriority tcb).val boostPrio.val⟩) := by
  cases hb : tcb.schedContextBinding with
  | unbound =>
    cases hboost : tcb.pipBoost <;>
      simp [resolveEffectivePrioDeadline, SystemState.threadBasePriority, hb, hboost]
  | bound scId =>
    cases hsc : st.getSchedContext? scId <;>
      cases hboost : tcb.pipBoost <;>
        simp [resolveEffectivePrioDeadline, SystemState.threadBasePriority, hb, hsc, hboost]
  | donated scId owner =>
    cases hsc : st.getSchedContext? scId <;>
      cases hboost : tcb.pipBoost <;>
        simp [resolveEffectivePrioDeadline, SystemState.threadBasePriority, hb, hsc, hboost]

-- WS-RR (`v0.35.133`) tombstone: `resolveEffectivePrioDeadline_fst_of_donated`
-- lived here.  Its conclusion is now `resolveEffectivePrioDeadline_fst_eq_boostedPriority`
-- at every binding, so a `.donated`-specific restatement would assert nothing its
-- unconditional form does not; the WS-OD payoff it carried — that the donee runs at
-- its OWN band — is what that theorem says everywhere.  Tier 3 refuses the name.

-- ============================================================================
-- R5.C (DEEP-SCH-02): Total effective-scheduling-parameter resolution
-- ============================================================================
--
-- Pre-R5, the two helpers `effectivePriority` (returned `Option (Priority ×
-- Deadline × DomainId)`) and `resolveEffectivePrioDeadline` (returns total
-- `Priority × Deadline`) diverged on how to handle a "bound thread with
-- missing SchedContext" — the former returned `none`, the latter fell back
-- to TCB fields.  The runtime-checked invariant
-- `schedContextStoreConsistent` (part of `crossSubsystemInvariant`) makes
-- this case unreachable, so both helpers were arguably correct in their
-- domains, but callers seeing one or the other API had to thread the
-- distinction.
--
-- R5.C unifies the convention by introducing `effectiveSchedParams` — a
-- total variant that always returns a triple by falling back to TCB
-- fields on SC-lookup failure (matching `resolveEffectivePrioDeadline`'s
-- discipline).
--
-- WS-RC R5.C.1 (DEEP-SCH-02) full deprecation: The partial
-- `effectivePriority` and its helper theorems are now RETIRED (see the
-- Z4-B section above).  Only the total `effectiveSchedParams` form
-- remains.

/-- R5.C (DEEP-SCH-02): Total effective-scheduling-parameter resolution.

Returns `(priority, deadline, domain)` unconditionally, and **which object
supplies each component is the WS-OD (v0.35.3) split**:
- `deadline` is **reservation-owned** and comes from the SchedContext the thread
  *runs on* (`SchedContextBinding.scId?`) at every binding, `.donated` included:
  being charged to a reservation and answering to its deadline is what a
  donation is.
- `priority` and `domain` are **thread-owned** and come from the SchedContext
  the thread *owns* (`ownScId?`), which is `.bound` alone, and otherwise from
  the TCB.  A donee therefore keeps its own scheduling band and its own
  partition — the latter matching what the scheduler actually does, since every
  live domain filter reads `tcb.domain`.
- For unbound threads or threads whose SC lookup fails (unreachable under
  `schedContextStoreConsistent`), the TCB fields are used throughout.
- PIP boost (`tcb.pipBoost`) is applied via `Nat.max` against the base
  priority, mirroring `resolveEffectivePrioDeadline`'s composition.

This is the canonical call-side API for any consumer that wants to read
"the thread's effective scheduling parameters".  Pre-R5.C.1, an `Option`
variant `effectivePriority` was retained for backward compatibility;
R5.C.1 retired that variant in favour of this total form. -/
@[inline] def effectiveSchedParams (st : SystemState) (tcb : TCB)
    : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId :=
  match tcb.schedContextBinding with
  | .unbound => (tcb.boostedPriority, tcb.deadline, tcb.domain)
  | .bound scId =>
    match st.getSchedContext? scId with
    -- WS-RR (`v0.35.133`): the boost is applied to the THREAD's base at every
    -- binding, because that is the only base there is -- one
    -- `Priority.raisedBy`, one base (`Prelude.lean`).
    --
    -- **WS-RR (`v0.35.136`): and the DOMAIN is the thread's at every binding
    -- too.**  `v0.35.133` left `sc.domain` here on the stated ground that "the
    -- domain mirror is a separate pair, with no writer known to break it", and
    -- PR #897's review found the writer: `schedContextConfigure` rewrites
    -- `sc.domain` while the reservation is **donated**, where its propagation is
    -- gated off (a donee's `ownScId?` is `none`), and
    -- `returnDonatedSchedContext` then rebinds the origin `.bound` with its own
    -- `tcb.domain` untouched.  So this arm reported a partition set by a holder
    -- of a capability on the RESERVATION rather than on the thread -- which is
    -- the v0.35.3 argument for the `.donated` arm below, arriving at the arm it
    -- left alone.  Free on the live tree: every domain filter reads
    -- `tcb.domain` (`chooseBestRunnableInDomainEffective`), so this component
    -- has no live consumer and the golden trace is byte-identical.
    | some sc => (tcb.boostedPriority, sc.deadline, tcb.domain)
    | none => (tcb.boostedPriority, tcb.deadline, tcb.domain)
  | .donated scId _ =>
    -- WS-OD (v0.35.3): the donor's **deadline** — the reservation-owned
    -- parameter a donee is charged against — and the donee's own priority and
    -- domain, which are thread-owned (`SchedContextBinding.ownScId?`).  Domain
    -- is not cosmetic here: `chooseBestRunnableInDomainEffective` and every
    -- other live domain filter read `tcb.domain`, so reporting `sc.domain` for
    -- a donee described a partition the scheduler never puts it in.
    -- `effectiveSchedParams_priority_deadline_eq_resolve` pins the priority and
    -- deadline against `resolveEffectivePrioDeadline`.
    match st.getSchedContext? scId with
    | some sc => (tcb.boostedPriority, sc.deadline, tcb.domain)
    | none => (tcb.boostedPriority, tcb.deadline, tcb.domain)

/-- WS-ZA ZA4.5: the effective parameters read no run-queue link. -/
theorem effectiveSchedParams_of_objectsAgreeOffRunLinks
    (st st' : SystemState) (tcb : TCB) (h : st'.objectsAgreeOffRunLinks st) :
    effectiveSchedParams st' tcb = effectiveSchedParams st tcb := by
  unfold effectiveSchedParams
  simp only [h.getSchedContext?]

/-- R5.C: `effectiveSchedParams` agrees with `resolveEffectivePrioDeadline`
on the `(priority, deadline)` pair. The third component (`domain`) is
unique to `effectiveSchedParams`. This is the bridge that lets callers
switch between the two without changing behaviour. -/
theorem effectiveSchedParams_priority_deadline_eq_resolve
    (st : SystemState) (tcb : TCB) :
    ((effectiveSchedParams st tcb).1, (effectiveSchedParams st tcb).2.1)
      = resolveEffectivePrioDeadline st tcb := by
  -- The two helpers compose the same priority/deadline shape over identical
  -- branches; the difference is only on the third (domain) component, which
  -- is projected away on the LHS.
  -- Since `v0.35.28` both sides apply the boost through `Priority.raisedBy`
  -- rather than through an inline `match tcb.pipBoost`, so the branch structure
  -- to split is the binding and (where there is one) the SchedContext lookup:
  -- one level shallower than it was, and the same on both sides.
  simp only [effectiveSchedParams, resolveEffectivePrioDeadline]
  split <;> (first | rfl | (split <;> rfl))

/-- The priority component, as the two-component resolver reports it. -/
theorem effectiveSchedParams_fst_eq_resolve (st : SystemState) (tcb : TCB) :
    (effectiveSchedParams st tcb).1 = (resolveEffectivePrioDeadline st tcb).1 := by
  rw [← effectiveSchedParams_priority_deadline_eq_resolve]

/-- The deadline component, as the two-component resolver reports it. -/
theorem effectiveSchedParams_snd_fst_eq_resolve (st : SystemState) (tcb : TCB) :
    (effectiveSchedParams st tcb).2.1 = (resolveEffectivePrioDeadline st tcb).2 := by
  rw [← effectiveSchedParams_priority_deadline_eq_resolve]

/-- R5.C: `effectiveSchedParams` is total. -/
theorem effectiveSchedParams_total (st : SystemState) (tcb : TCB) :
    ∃ triple, effectiveSchedParams st tcb = triple :=
  ⟨_, rfl⟩

/-- **The resolver's priority component IS `TCB.boostedPriority`**, at every
binding and whatever the store holds -- `resolveEffectivePrioDeadline_fst_eq_boostedPriority`'s
sibling for the triple-valued resolver, and the fact that makes the frozen
surface able to answer the same question.

`v0.35.133` gave a base priority one home, so all five of this helper's arms
compose the boost against `tcb.priority`; the deadline and the domain still come
from a SchedContext on some of them, which is why this is stated on the first
component alone.  **Derived** from the pair bridge above rather than re-split
over the arms, so the two resolvers cannot come to disagree about the priority
without this failing to elaborate.

Its consumer is `FrozenOps.Agreement`'s
`frozenComputeMaxWaiterPriority_eq_live_reading`: the frozen waiter fold reads
`TCB.boostedPriority` directly because that surface resolves no scheduling
parameters, and that is the *same* reading only while this holds.  PR #897's
review reported the pair as a divergence, correctly against `v0.35.132` and no
longer against `v0.35.133` -- with nothing in the tree saying so, which is what
this closes. -/
theorem effectiveSchedParams_fst_eq_boostedPriority (st : SystemState) (tcb : TCB) :
    (effectiveSchedParams st tcb).1 = tcb.boostedPriority := by
  have hPair := effectiveSchedParams_priority_deadline_eq_resolve st tcb
  have hFst : (effectiveSchedParams st tcb).1 = (resolveEffectivePrioDeadline st tcb).1 :=
    congrArg Prod.fst hPair
  rw [hFst, resolveEffectivePrioDeadline_fst_eq_boostedPriority]

/-- **WS-RR (`v0.35.136`): the reported domain is the THREAD's, at every
binding** — the third component's counterpart to the first's pin above, and the
statement that closes the mirror `v0.35.133` left on the `.bound` arm.

It is stated rather than left to be read off the definition for the reason that
cut records about the priority half: the *readers* are what make a two-homed
field a hazard, so a cut that sends this component back to consulting a
reservation must fail to elaborate rather than merely look different.  A
reservation's `domain` survives on the write side alone, as the partition
`schedContextBind` requires a thread to already be in (`tcb.domain != sc.domain`
is that bind's own refusal) and `schedContextConfigureBoundPropagate` moves it
to; nothing reads it as a running thread's partition.

PR #897's review is what made this necessary rather than tidy: the pop rebinds
an origin `.bound` without touching either field, so a `schedContextConfigure`
of a **donated** reservation — whose propagation is gated off, the donee's
`ownScId?` being `none` — left the pair disagreeing on a state the kernel
reaches.  `boundThreadDomainConsistent` is therefore no more an invariant than
`boundThreadPriorityConsistent` is; both are facts about their writers, and
`returnDonatedSchedContext_refutes_boundThreadConsistency`
(`SeLe4n/Kernel/IPC/Operations/Endpoint.lean`) is the refutation that keeps a
later cut from assuming either across a pop. -/
theorem effectiveSchedParams_domain_eq (st : SystemState) (tcb : TCB) :
    (effectiveSchedParams st tcb).2.2 = tcb.domain := by
  -- One `split` per matcher: the binding first, then (on the two arms that read
  -- the store) the lookup, and every leaf is a literal triple whose third
  -- component is `tcb.domain`.  `split` exposes the inner scrutinee that a
  -- `cases` on it cannot reach, since it sits under the outer matcher's binder.
  unfold effectiveSchedParams
  split <;> (try split) <;> rfl


/-- AG1-A: Resolve the effective insertion priority for RunQueue re-enqueue.

When a thread is re-inserted into the RunQueue (budget refill, yield, bind),
the insertion priority must account for PIP boost — not just the base
SchedContext priority. This helper looks up the thread's TCB and calls
`resolveEffectivePrioDeadline` to get the correct effective priority.

If the TCB lookup fails (invariant violation — unreachable under
`crossSubsystemInvariant`), falls back to `sc.priority` for safety. -/
@[inline] def resolveInsertPriority (st : SystemState) (tid : SeLe4n.ThreadId)
    (sc : SchedContext) : SeLe4n.Priority :=
  -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
  match st.getTcb? tid with
  | some tcb => (resolveEffectivePrioDeadline st tcb).1
  | none     => sc.priority  -- defensive fallback

section
set_option linter.unusedSimpArgs false

/-- AK2-A/AK2-B bridge: the bucket a thread is keyed by **is** the priority
selection reads.

**WS-RR (`v0.35.133`): this pin held two resolvers together and now holds one.**
`effectiveBucketPriority` mirrored `resolveEffectivePrioDeadline`'s
classification because `Invariant.lean` sits below this module and could not
call it; with `TCB.priority` the only home both are `TCB.boostedPriority`, so
what remains to split is the shape of `resolveEffectivePrioDeadline`'s own
`match`, whose every arm now yields the same base. -/
theorem effectiveBucketPriority_eq_resolveEffective
    (st : SystemState) (tcb : TCB) :
    effectiveBucketPriority st tcb = (resolveEffectivePrioDeadline st tcb).1 := by
  unfold effectiveBucketPriority resolveEffectivePrioDeadline TCB.boostedPriority
  cases hBind : tcb.schedContextBinding with
  | unbound => simp only [hBind]
  | bound scId =>
    simp only [hBind]
    cases hSc : st.getSchedContext? scId <;> simp only [hSc]
  | donated scId owner =>
    simp only [hBind]
    cases hSc : st.getSchedContext? scId <;> simp only [hSc]


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
      match st.getTcb? tid with
      | some tcb =>
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
      -- WS-SM SM8.B (PR #861 review round 15): skip, do not fail — see
      -- `chooseBestRunnableBy` above for why.  This budget-aware variant is the
      -- one the live SGI handler reaches (`chooseThreadEffectiveOnCore` →
      -- `handleRescheduleSgiOnCore`), so it carries the same hazard and takes
      -- the same repair; leaving the two arms different would be worse than
      -- either choice, since the two scans are meant to agree
      -- (`chooseBestRunnableEffective_eq_chooseBestRunnableBy`).
      | _ => chooseBestRunnableEffective st eligible rest best

/-- WS-SM SM8.B: the budget-aware scan never fails; it is the scan the live
SGI handler reaches (`chooseThreadEffectiveOnCore` → `handleRescheduleSgiOnCore`),
and a run-queue entry that resolves to no TCB is skipped. -/
theorem chooseBestRunnableEffective_always_ok
    (st : SystemState) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)),
      ∃ r, chooseBestRunnableEffective st eligible list best = .ok r := by
  intro list
  induction list with
  | nil => intro best; exact ⟨best, rfl⟩
  | cons hd tl ih =>
    intro best
    unfold chooseBestRunnableEffective
    cases st.getTcb? hd with
    | none => exact ih _
    | some _ => exact ih _

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

/-- WS-ZA ZA4.5: the bucket-first selection over a highest bucket and a whole
queue given as lists — `chooseBestInBucketEffective` with the queue's lists
(`chooseBestInBucketEffective_eq_walks`), and the selection over the lists
walked along the threads' run-queue links. -/
def chooseBestInWalksEffective
    (st : SystemState)
    (maxBucket all : List SeLe4n.ThreadId)
    (activeDomain : SeLe4n.DomainId) :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) :=
  match chooseBestRunnableInDomainEffective st maxBucket activeDomain none with
  | .error e => .error e
  | .ok (some result) => .ok (some result)
  | .ok none =>
    chooseBestRunnableInDomainEffective st all activeDomain none

theorem chooseBestInBucketEffective_eq_walks (st : SystemState) (rq : RunQueue)
    (activeDomain : SeLe4n.DomainId) :
    chooseBestInBucketEffective st rq activeDomain =
      chooseBestInWalksEffective st rq.maxPriorityBucket rq.toList activeDomain := rfl

/-- WS-SM SM5.A.1: per-core thread selection (plan
WS-SM SM5 §3.1).

The per-core analogue of `chooseThread`: selects the highest-priority
runnable thread in core `c`'s active scheduling domain, reading **only**
core `c`'s run-queue slot (`runQueueOnCore c`) and active-domain slot
(`activeDomainOnCore c`).  This single-core-slot read footprint is the
per-core-independence property proven in SM5.A.3
(`chooseThreadOnCore_perCore_independence`): the selection on core `c` is
unaffected by writes to any other core's scheduler slots.

It is a **pure read** — no state is threaded or mutated (the result is the
selection alone, not a `(choice, state)` pair).  The legacy `chooseThread`
(SM5.A.5) is this function specialised to `bootCoreId` and lifted into the
`Kernel` monad with the state threaded unchanged.

**Return type rationale, and what changed (PR #861 review rounds 15/40).**
The plan's pseudocode returns a bare `Option ThreadId`; the implementation
returns `Except KernelError (Option ThreadId)`, and that type is retained.

A run-queue entry that fails to resolve to a TCB is now **skipped**, not
surfaced as `.schedulerInvariantViolation`.  The earlier contract said the
opposite, and the reason for the change is that surfacing it was not
fail-closed in practice: round 15 found that a retype could leave a destroyed
thread's id in a secondary core's queue, after which the error failed that
core's *entire* selection scan on every later call, with nothing ever removing
the entry — the core was wedged permanently.  Skipping the entry keeps
selection total (`chooseBestRunnableBy_always_ok` and its effective sibling
`chooseBestRunnableEffective_always_ok`) so a corrupt entry costs one
candidate rather than the core.

The consequence for callers is that a malformed queue is **not** reported here;
`runnableThreadsAreTCBs` remains the invariant that says such an entry cannot
arise, and `chooseThreadOnCore_ok_of_runnableTCBs` (SM5.A.4) still relates the
two.  The error type is kept because the *effective* selector can still fail
for budget-resolution reasons, and because narrowing it would churn every
caller for no gain.

Selection policy is identical to `chooseThread`: bucket-first
priority/EDF/FIFO via `chooseBestInBucket` (no budget filter — the
budget-aware variant is `chooseThreadEffective`). -/
noncomputable def chooseThreadOnCore (st : SystemState) (c : CoreId) :
    Except KernelError (Option SeLe4n.ThreadId) :=
  match chooseBestInBucket st.getObject? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some (tid, _, _)) => .ok (some tid)

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
noncomputable def chooseThread : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    match chooseThreadOnCore st bootCoreId with
    | .error e => .error e
    | .ok result => .ok (result, st)

/-- WS-SM SM5.A.5: the legacy single-core `chooseThread` is exactly the
per-core selection `chooseThreadOnCore` specialised to the boot core,
lifted into the `Kernel` monad (`chooseThread` is a pure read, so the
state is threaded unchanged).  `rfl` because that is now the literal
definition; this names the migration so downstream rewrites can appeal to
it without re-`unfold`ing both layers. -/
theorem chooseThread_eq_chooseThreadOnCore_bootCore (st : SystemState) :
    chooseThread st =
      (match chooseThreadOnCore st bootCoreId with
       | .error e => .error e
       | .ok result => .ok (result, st)) := rfl

/-- WS-SM SM5.A (budget-aware companion to `chooseThreadOnCore`): per-core
SchedContext-aware thread selection.

The per-core analogue of `chooseThreadEffective`: selects the
highest-*effective*-priority runnable thread in core `c`'s active domain that
also has sufficient CBS budget, reading only core `c`'s run-queue slot and
active-domain slot (plus the global object store for the SchedContext/budget
lookups, which is held under the implicit ObjStore lock like every
transition).  Pure read.

Unlike `chooseThreadOnCore` (which mirrors the non-budget `chooseThread`),
this respects CBS budgets via `hasSufficientBudget` — a thread whose
SchedContext budget is exhausted is **not** selected.  The legacy
`chooseThreadEffective` is this function specialised to `bootCoreId` and
lifted into the `Kernel` monad.  Returns `Except KernelError (Option
ThreadId)` for the same fail-closed reason as `chooseThreadOnCore`. -/
def chooseThreadEffectiveOnCore (st : SystemState) (c : CoreId) :
    Except KernelError (Option SeLe4n.ThreadId) :=
  match chooseBestInWalksEffective st (st.runMaxBucketWalk c) (st.runQueueWalk c)
      (st.scheduler.activeDomainOnCore c) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some (tid, _, _)) => .ok (some tid)

/-- WS-ZA ZA4.5: the selection walks the threads' run-queue links; where they
agree with core `c`'s queue (`runQueueRefinedOnCore`) it is the bucket-first
scan of the queue itself. -/
theorem chooseThreadEffectiveOnCore_eq_queue {st : SystemState} {c : CoreId}
    (hR : st.runQueueRefinedOnCore c) :
    chooseThreadEffectiveOnCore st c =
      match chooseBestInBucketEffective st (st.scheduler.runQueueOnCore c)
          (st.scheduler.activeDomainOnCore c) with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some (tid, _, _)) => .ok (some tid) := by
  unfold chooseThreadEffectiveOnCore
  rw [hR.runMaxBucketWalk_eq, hR.runQueueWalk_eq]; rfl

/-- WS-ZA ZA4.5: `chooseThreadOnCore` read along the threads' run-queue links,
so it has executable code; equal to it wherever the links refine core `c`'s
queue (`chooseThreadOnCoreByLinks_eq`). -/
def chooseThreadOnCoreByLinks (st : SystemState) (c : CoreId) :
    Except KernelError (Option SeLe4n.ThreadId) :=
  match (match chooseBestRunnableInDomain st.getObject? (st.runMaxBucketWalk c)
            (st.scheduler.activeDomainOnCore c) none with
         | .error e => Except.error e
         | .ok (some result) => Except.ok (some result)
         | .ok none => chooseBestRunnableInDomain st.getObject? (st.runQueueWalk c)
            (st.scheduler.activeDomainOnCore c) none) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some (tid, _, _)) => .ok (some tid)

theorem chooseThreadOnCoreByLinks_eq {st : SystemState} {c : CoreId}
    (hR : st.runQueueRefinedOnCore c) :
    chooseThreadOnCoreByLinks st c = chooseThreadOnCore st c := by
  unfold chooseThreadOnCoreByLinks chooseThreadOnCore chooseBestInBucket
  rw [hR.runMaxBucketWalk_eq, hR.runQueueWalk_eq]

/-- WS-ZA ZA4.5: **the selection scan with the best candidate in scalars.**
`chooseBestRunnableEffective` carries the best candidate as an
`Option (ThreadId × Priority × Deadline)` and returns it in an `Except`, so each
improvement builds a record and the result two more; this scan carries whether
a candidate was found and its thread, priority and deadline as separate
arguments and returns only the chosen thread's code, `0` for none and `t + 1`
for `t` (`chooseBestRunnableEffectiveCode_eq`). -/
def chooseBestRunnableEffectiveCode (st : SystemState) (eligible : TCB → Bool) :
    List SeLe4n.ThreadId → Bool → SeLe4n.ThreadId → SeLe4n.Priority → SeLe4n.Deadline → Nat
  | [], found, bt, _, _ => if found then bt.val + 1 else 0
  | tid :: rest, found, bt, bp, bd =>
      match st.getTcb? tid with
      | some tcb =>
          if eligible tcb && hasSufficientBudget st tcb then
            let pd := resolveEffectivePrioDeadline st tcb
            if !found || isBetterCandidate bp bd pd.1 pd.2 then
              chooseBestRunnableEffectiveCode st eligible rest true tid pd.1 pd.2
            else chooseBestRunnableEffectiveCode st eligible rest found bt bp bd
          else chooseBestRunnableEffectiveCode st eligible rest found bt bp bd
      | none => chooseBestRunnableEffectiveCode st eligible rest found bt bp bd

/-- The code of the thread a selection result names: `0` for none (or a failed
scan, which `chooseBestRunnableEffective_always_ok` rules out), `t + 1` for `t`. -/
def selectionCode :
    Except KernelError (Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)) → Nat
  | .ok (some (t, _, _)) => t.val + 1
  | _ => 0

theorem chooseBestRunnableEffectiveCode_eq (st : SystemState) (eligible : TCB → Bool)
    (l : List SeLe4n.ThreadId) (found : Bool) (bt : SeLe4n.ThreadId) (bp : SeLe4n.Priority)
    (bd : SeLe4n.Deadline) :
    chooseBestRunnableEffectiveCode st eligible l found bt bp bd =
      selectionCode (chooseBestRunnableEffective st eligible l
        (if found then some (bt, bp, bd) else none)) := by
  induction l generalizing found bt bp bd with
  | nil => cases found <;> rfl
  | cons tid rest ih =>
    unfold chooseBestRunnableEffectiveCode chooseBestRunnableEffective
    cases hT : st.getTcb? tid with
    | none => simp only [ih]
    | some tcb =>
      simp only
      by_cases hE : (eligible tcb && hasSufficientBudget st tcb) = true
      · rw [if_pos hE, if_pos hE]
        cases found
        · simp only [Bool.not_false, Bool.true_or, if_true, ih]; rfl
        · simp only [Bool.not_true, Bool.false_or, if_true]
          split
          · rw [ih]; simp only [if_true]
          · rw [ih]; simp only [if_true]
      · rw [if_neg hE, if_neg hE, ih]

/-- WS-ZA ZA4.5: core `c`'s selection as a thread code, the bucket-first scan of
`chooseBestInBucketEffective` run through `chooseBestRunnableEffectiveCode`
(`chooseThreadEffectiveOnCore_eq_code`). -/
def chooseThreadEffectiveOnCoreCode (st : SystemState) (c : CoreId) : Nat :=
  let dom := st.scheduler.activeDomainOnCore c
  match chooseBestRunnableEffectiveCode st (fun tcb => tcb.domain == dom)
      (st.runMaxBucketWalk c) false default default default with
  | 0 => chooseBestRunnableEffectiveCode st (fun tcb => tcb.domain == dom)
      (st.runQueueWalk c) false default default default
  | k => k

theorem chooseThreadEffectiveOnCore_eq_code (st : SystemState) (c : CoreId) :
    chooseThreadEffectiveOnCore st c =
      match chooseThreadEffectiveOnCoreCode st c with
      | 0 => .ok none
      | k + 1 => .ok (some ⟨k⟩) := by
  unfold chooseThreadEffectiveOnCore chooseBestInWalksEffective chooseThreadEffectiveOnCoreCode
    chooseBestRunnableInDomainEffective
  simp only [chooseBestRunnableEffectiveCode_eq, Bool.false_eq_true, if_false]
  obtain ⟨r1, h1⟩ := chooseBestRunnableEffective_always_ok st
    (fun tcb => tcb.domain == st.scheduler.activeDomainOnCore c)
    (st.runMaxBucketWalk c) none
  rw [h1]
  cases r1 with
  | some r => obtain ⟨t, p, d⟩ := r; rfl
  | none =>
    obtain ⟨r2, h2⟩ := chooseBestRunnableEffective_always_ok st
      (fun tcb => tcb.domain == st.scheduler.activeDomainOnCore c)
      (st.runQueueWalk c) none
    rw [h2]
    cases r2 with
    | some r => obtain ⟨t, p, d⟩ := r; rfl
    | none => rfl

/-- WS-ZA ZA4.5: the deadline `resolveEffectivePrioDeadline` resolves, alone:
the bound or donated SchedContext's when it resolves, else the thread's own. -/
@[inline] def effectiveDeadlineOf (st : SystemState) (tcb : TCB) : SeLe4n.Deadline :=
  match tcb.schedContextBinding with
  | .unbound => tcb.deadline
  | .bound scId =>
      match st.getSchedContext? scId with
      | some sc => sc.deadline
      | none => tcb.deadline
  | .donated scId _ =>
      match st.getSchedContext? scId with
      | some sc => sc.deadline
      | none => tcb.deadline

/-- `resolveEffectivePrioDeadline` as its two halves, so a scan can read them
without building the pair. -/
theorem resolveEffectivePrioDeadline_eq (st : SystemState) (tcb : TCB) :
    resolveEffectivePrioDeadline st tcb =
      (tcb.priority.raisedBy tcb.pipBoost, effectiveDeadlineOf st tcb) := by
  unfold resolveEffectivePrioDeadline effectiveDeadlineOf
  cases hb : tcb.schedContextBinding with
  | unbound => simp [hb]
  | bound scId => cases hs : st.getSchedContext? scId <;> simp [hs]
  | donated scId _ => cases hs : st.getSchedContext? scId <;> simp [hs]

/-- WS-ZA ZA4.5: **the code scan walking the threads' run-queue links.**  The
scan `chooseBestRunnableEffectiveCode` runs over the threads in the domain
`dom`, each read once from the object store with its link on core `c` read off
the same TCB — along the bucket links when `bucket` holds, else along the
queue links — from code `k` for at most `n` steps, with no list and no closure
built (`chooseOnLinksCode_eq`). -/
def chooseOnLinksCode (st : SystemState) (dom : SeLe4n.DomainId) (c : CoreId) (bucket : Bool) :
    Nat → Nat → Bool → SeLe4n.ThreadId → SeLe4n.Priority → SeLe4n.Deadline → Nat
  | 0, _, found, bt, _, _ => if found then bt.val + 1 else 0
  | _ + 1, 0, found, bt, _, _ => if found then bt.val + 1 else 0
  | n + 1, k + 1, found, bt, bp, bd =>
      let tid : SeLe4n.ThreadId := ⟨k⟩
      match st.getTcb? tid with
      | some tcb =>
          let nx := tcb.runNextOn c bucket
          if (tcb.domain == dom) && hasSufficientBudget st tcb then
            let pp := tcb.priority.raisedBy tcb.pipBoost
            let pdl := effectiveDeadlineOf st tcb
            if !found || isBetterCandidate bp bd pp pdl then
              chooseOnLinksCode st dom c bucket n nx true tid pp pdl
            else chooseOnLinksCode st dom c bucket n nx found bt bp bd
          else chooseOnLinksCode st dom c bucket n nx found bt bp bd
      | none => chooseOnLinksCode st dom c bucket n 0 found bt bp bd

theorem chooseOnLinksCode_eq (st : SystemState) (dom : SeLe4n.DomainId) (c : CoreId)
    (bucket : Bool) (n k : Nat)
    (found : Bool) (bt : SeLe4n.ThreadId) (bp : SeLe4n.Priority) (bd : SeLe4n.Deadline) :
    chooseOnLinksCode st dom c bucket n k found bt bp bd =
      chooseBestRunnableEffectiveCode st (fun tcb => tcb.domain == dom)
        (LinkedQueue.walk (fun t => if bucket then (st.runLinkOn c t).bucketNext
          else (st.runLinkOn c t).next) n k) found bt bp bd := by
  induction n generalizing k found bt bp bd with
  | zero => rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      cases hT : st.getTcb? ⟨k⟩ with
      | none =>
        have hL : st.runLinkOn c ⟨k⟩ = RunQueue.RunQueueLink.none := by
          unfold SystemState.runLinkOn; rw [hT]
        simp only [chooseOnLinksCode, LinkedQueue.walk, chooseBestRunnableEffectiveCode, hT, ih,
          hL]
        cases bucket <;> rfl
      | some tcb =>
        have hL : st.runLinkOn c ⟨k⟩ = tcb.runLinkOn c := by
          unfold SystemState.runLinkOn; rw [hT]
        simp only [chooseOnLinksCode, LinkedQueue.walk, chooseBestRunnableEffectiveCode, ih, hT,
          hL, resolveEffectivePrioDeadline_eq, TCB.runNextOn_eq]

/-- WS-ZA ZA4.5: core `c`'s selection code read straight off the threads'
run-queue links and the core's ends: the max-priority bucket through its
bucket links, then the whole queue through its queue links, each bounded by the
queue's size.  Equal to `chooseThreadEffectiveOnCoreCode`
(`chooseThreadEffectiveOnCoreCode_eq_walk`), which the compiler runs in its
place. -/
def chooseThreadEffectiveOnCoreCodeWalk (st : SystemState) (c : CoreId) : Nat :=
  let e := st.scheduler.runQueueEndsOnCore c
  let dom := st.scheduler.activeDomainOnCore c
  let bucketHead := if e.maxCode = 0 then 0
    else (RunQueue.endsOf e.buckets ⟨e.maxCode - 1⟩).head
  match chooseOnLinksCode st dom c true e.size bucketHead false default default default with
  | 0 => chooseOnLinksCode st dom c false e.size e.head false default default default
  | k => k

@[csimp] theorem chooseThreadEffectiveOnCoreCode_eq_walk :
    @chooseThreadEffectiveOnCoreCode = @chooseThreadEffectiveOnCoreCodeWalk := by
  funext st c
  unfold chooseThreadEffectiveOnCoreCode chooseThreadEffectiveOnCoreCodeWalk
    SystemState.runMaxBucketWalk SystemState.runQueueWalk
  simp only [chooseOnLinksCode_eq, Bool.false_eq_true, if_true, if_false]

/-- Z4-D/E: SchedContext-aware thread selection.

Uses `chooseBestInBucketEffective` which filters by budget eligibility and
resolves effective priorities from SchedContext objects. This is used by the
extended scheduler operations (`scheduleEffective`, `timerTickWithBudget`,
`handleYieldWithBudget`). The original `chooseThread` is preserved for
backward compatibility with existing preservation proofs.

WS-SM SM5.A: now defined as the per-core `chooseThreadEffectiveOnCore`
specialised to the boot core (symmetric with the `chooseThread` migration). -/
def chooseThreadEffective : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    match chooseThreadEffectiveOnCore st bootCoreId with
    | .error e => .error e
    | .ok result => .ok (result, st)

/-- WS-SM SM5.A: the legacy `chooseThreadEffective` is exactly the per-core
budget-aware selection specialised to the boot core, lifted into the `Kernel`
monad. `rfl` by definition. -/
theorem chooseThreadEffective_eq_chooseThreadEffectiveOnCore_bootCore (st : SystemState) :
    chooseThreadEffective st =
      (match chooseThreadEffectiveOnCore st bootCoreId with
       | .error e => .error e
       | .ok result => .ok (result, st)) := rfl

/-- Z4-D/E: `chooseThreadEffective` is read-only — preserves state. -/
theorem chooseThreadEffective_preserves_state
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hStep : chooseThreadEffective st = .ok (next, st')) :
    st' = st := by
  unfold chooseThreadEffective chooseThreadEffectiveOnCore at hStep
  cases hPick : chooseBestInWalksEffective st (st.runMaxBucketWalk bootCoreId)
      (st.runQueueWalk bootCoreId) (st.scheduler.activeDomainOnCore bootCoreId) with
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
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => st
  | some outTid =>
      -- One TCB rewritten in place through the lookup that is its own witness.
      st.updateTcb outTid fun outTcb => { outTcb with registerContext := st.machine.regs }

/-- V5-D (M-DEF-4): Checked variant of `saveOutgoingContext` that returns a
    success indicator. Returns `(state, true)` on successful save (or no current
    thread), `(state, false)` when the current thread's TCB lookup fails.

    Under `currentThreadValid`, the `false` branch is unreachable. This variant
    exists for defense-in-depth: callers at API boundaries can assert on the
    success flag to surface invariant violations early. -/
def saveOutgoingContextChecked (st : SystemState) : SystemState × Bool :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => (st, true)
  | some outTid =>
      match st.getTcbWitnessed? outTid with
      | some ⟨outTcb, h⟩ =>
          (st.rewriteObject outTid.toObjId
              (.tcb { outTcb with registerContext := st.machine.regs })
              (SystemState.rewriteAdmissible_tcb h _),
           true)
      | none => (st, false)

/-- AI3-C (L-09): Under `currentThreadValid`, `saveOutgoingContext` always succeeds.
The silent-return-on-TCB-miss path (line 495) is unreachable because
`currentThreadValid` guarantees the current thread resolves to a TCB.

This theorem formally proves the unreachability, making the design decision
explicit: the unchecked variant is safe under invariants, and the checked
variant (`saveOutgoingContextChecked`) provides defense-in-depth at API
boundaries.

Design rationale for keeping `SystemState` return type (not `Except`):
- 20+ preservation theorems unfold `saveOutgoingContext` by name
- Changing to `Except` would require cascading updates through `schedule`,
  `scheduleEffective`, `switchDomain`, and all their callers (~100 proof sites)
- The unreachability proof below provides equivalent formal assurance
- `saveOutgoingContextChecked` at API boundaries catches any invariant violation -/
theorem saveOutgoingContext_always_succeeds_under_currentThreadValid
    (st : SystemState)
    (hCTV : currentThreadValid st) :
    (saveOutgoingContextChecked st).2 = true := by
  unfold saveOutgoingContextChecked currentThreadValid at *
  cases hCur : (st.scheduler.currentOnCore bootCoreId) with
  | none => rfl
  | some outTid =>
    simp only [hCur] at hCTV
    obtain ⟨tcb, hTcb⟩ := hCTV
    -- `currentThreadValid` is stated over the store; the transition reads
    -- through the witnessed `getTcb?`, so the witness crosses by the accessor's
    -- own iff and the witnessed lookup's equation.
    simp only [SystemState.getTcbWitnessed?_eq_some
      ((SystemState.getTcb?_eq_some_iff st outTid tcb).mpr hTcb)]

/-- V5-D: The checked variant agrees with the unchecked variant on the state component. -/
theorem saveOutgoingContextChecked_fst_eq (st : SystemState) :
    (saveOutgoingContextChecked st).1 = saveOutgoingContext st := by
  unfold saveOutgoingContextChecked saveOutgoingContext
  cases (st.scheduler.currentOnCore bootCoreId) with
  | none => rfl
  | some outTid =>
      -- Two-way on the accessor both sides read, through the witnessed lookup's
      -- two equations and the typed update's two.
      cases h : st.getTcb? outTid with
      | none =>
          simp only [SystemState.getTcbWitnessed?_eq_none h, SystemState.updateTcb_eq_self_of_none h]
      | some t =>
          simp only [SystemState.getTcbWitnessed?_eq_some h, SystemState.updateTcb_eq_of_some h]
          rfl

/-- WS-H12c/H-03/V5-E: Restore the incoming thread's register context into the
machine register file. If the incoming TCB is not found, returns the state
unchanged (unreachable under `currentThreadValid`).

V5-E (M-DEF-5): When the TCB lookup fails, the restore is silently skipped.
Under `currentThreadValid`, this branch is unreachable. The checked variant
`restoreIncomingContextChecked` provides an explicit success indicator. -/
def restoreIncomingContext (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some inTcb =>
      { st with machine := st.machine.setRegsOnCore bootCoreId inTcb.registerContext }
  | none => st

/-- V5-E (M-DEF-5): Checked variant of `restoreIncomingContext` that returns a
    success indicator. Returns `(state, true)` on successful restore,
    `(state, false)` when the thread's TCB lookup fails.

    Under `currentThreadValid`, the `false` branch is unreachable. -/
def restoreIncomingContextChecked (st : SystemState)
    (tid : SeLe4n.ThreadId) : SystemState × Bool :=
  match st.getTcb? tid with
  | some inTcb =>
      ({ st with machine := st.machine.setRegsOnCore bootCoreId inTcb.registerContext }, true)
  | none => (st, false)

/-- V5-E: The checked variant agrees with the unchecked variant on the state component. -/
theorem restoreIncomingContextChecked_fst_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (restoreIncomingContextChecked st tid).1 = restoreIncomingContext st tid := by
  unfold restoreIncomingContextChecked restoreIncomingContext
  cases h : st.getTcb? tid with
  | none => simp_all
  | some _ => simp_all

-- ============================================================================
-- WS-SM SM5.I — per-core context restore (writes the *operated* core's bank)
-- ============================================================================

/-- WS-SM SM5.I (per-core register banks): restore `tid`'s register context into
**core `c`'s** register bank.  The per-core analogue of `restoreIncomingContext`
(which writes the boot core's bank via the SM5.I `MachineState.regs` accessor);
the per-core scheduler dispatch (`switchToThreadOnCore`, `scheduleEffectiveOnCore`,
`dispatchIdleOnCore`) uses this so each core's bank holds its **own** current
thread's context — the substance behind the `∀ c` `contextMatchesCurrentOnCore`
invariant (a dispatch on core `c` touches only `c`'s bank, leaving every sibling
core's bank framed). -/
def restoreIncomingContextOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some inTcb =>
      { st with machine := st.machine.setRegsOnCore c inTcb.registerContext }
  | none => st

/-- WS-ZA ZA4: **the compiled restore.**  The incoming thread's words are
written into the file the core's bank already owns (`modifyRegsOnCore`,
`RegisterFile.overwriteWith`) rather than the bank taking the thread's file:
a file both held would be shared, and the next trap's save into either
(`InFlightContext.snapshotInto`) would copy it. -/
def restoreIncomingContextOnCoreImpl (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some inTcb =>
      let m := st.machine.modifyRegsOnCore c (SeLe4n.RegisterFile.overwriteWith inTcb.registerContext)
      { st with machine := m }
  | none => st

@[csimp] theorem restoreIncomingContextOnCore_eq_impl :
    @restoreIncomingContextOnCore = @restoreIncomingContextOnCoreImpl := by
  funext st c tid
  unfold restoreIncomingContextOnCore restoreIncomingContextOnCoreImpl
  split
  · simp only [MachineState.modifyRegsOnCore_eq, SeLe4n.RegisterFile.overwriteWith_eq]
  · rfl

/-- WS-SM SM5.I: the per-core restore leaves the scheduler unchanged. -/
@[simp] theorem restoreIncomingContextOnCore_scheduler (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : (restoreIncomingContextOnCore st c tid).scheduler = st.scheduler := by
  unfold restoreIncomingContextOnCore; split <;> rfl

/-- WS-SM SM5.I: the per-core restore leaves the object store unchanged. -/
@[simp] theorem restoreIncomingContextOnCore_objects (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : (restoreIncomingContextOnCore st c tid).objects = st.objects := by
  unfold restoreIncomingContextOnCore; split <;> rfl

/-- WS-SM SM5.I: the per-core restore frames every thread's TCB resolution. -/
theorem restoreIncomingContextOnCore_getTcb? (st : SystemState) (c : CoreId)
    (tid t : SeLe4n.ThreadId) : (restoreIncomingContextOnCore st c tid).getTcb? t = st.getTcb? t := by
  unfold SystemState.getTcb?; rw [restoreIncomingContextOnCore_objects]

/-- WS-SM SM5.I: the per-core restore leaves the machine timer unchanged. -/
@[simp] theorem restoreIncomingContextOnCore_machine_timer (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    (restoreIncomingContextOnCore st c tid).machine.timer = st.machine.timer := by
  unfold restoreIncomingContextOnCore; split
  · exact MachineState.setRegsOnCore_timer _ _ _
  · rfl

/-- WS-SM SM5.I: at the boot core the per-core restore coincides with the
single-core `restoreIncomingContext` (definitional bridge). -/
theorem restoreIncomingContextOnCore_bootCore (st : SystemState) (tid : SeLe4n.ThreadId) :
    restoreIncomingContextOnCore st bootCoreId tid = restoreIncomingContext st tid := rfl

/-- WS-SM SM5.I (contextMatches establishment): after restoring `tid` (a TCB) on
core `c`, core `c`'s register bank equals `tid`'s saved register context. -/
theorem restoreIncomingContextOnCore_regsOnCore_self (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) :
    (restoreIncomingContextOnCore st c tid).machine.regsOnCore c = tcb.registerContext := by
  -- The transition discriminates on `getTcb?` itself, so the caller's typed
  -- hypothesis drives the match directly; no crossing to the store form.
  simp only [restoreIncomingContextOnCore, hTcb,
    MachineState.regsOnCore_setRegsOnCore_self]

/-- WS-SM SM5.I (sibling-core frame): the per-core restore on core `c` leaves
every *other* core's register bank untouched. -/
theorem restoreIncomingContextOnCore_regsOnCore_ne (st : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) (h : c ≠ c') :
    (restoreIncomingContextOnCore st c tid).machine.regsOnCore c' = st.machine.regsOnCore c' := by
  unfold restoreIncomingContextOnCore; split
  · exact MachineState.regsOnCore_setRegsOnCore_ne _ c c' _ h
  · rfl

/-- WS-SM SM5.B (PR #814 review P2-1, self-switch guard): restore `tid`'s saved
register context into core `c`'s bank **unless** `tid` is already core `c`'s
current (running) thread.  A running thread's authoritative registers live in
`regsOnCore c`; its saved `registerContext` may be stale until the next context
save, so restoring it on a self-switch would roll the running context back at the
hardware/FFI refinement boundary.  In the abstract model the two agree for the
current thread (the maintained `contextMatchesCurrentOnCore` invariant gives
`regsOnCore c == registerContext`), so the guard changes no reachable model
behaviour — it makes the transition hardware-faithful.  Writes only
`machine.coreRegs` (and only off the self-switch). -/
def restoreIncomingContextOnCoreUnlessCurrent (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : SystemState :=
  if st.scheduler.currentOnCore c == some tid then st
  else restoreIncomingContextOnCore st c tid

/-- WS-ZA ZA4.7: the compiled `restoreIncomingContextOnCoreUnlessCurrent`: the
current slot is compared in place (`Option.isEqSome`), with no `some tid` cell
built to compare against. -/
def restoreIncomingContextOnCoreUnlessCurrentImpl (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : SystemState :=
  if (st.scheduler.currentOnCore c).isEqSome tid then st
  else restoreIncomingContextOnCore st c tid

@[csimp] theorem restoreIncomingContextOnCoreUnlessCurrent_eq_impl :
    @restoreIncomingContextOnCoreUnlessCurrent = @restoreIncomingContextOnCoreUnlessCurrentImpl := by
  funext st c tid
  unfold restoreIncomingContextOnCoreUnlessCurrent restoreIncomingContextOnCoreUnlessCurrentImpl
  cases st.scheduler.currentOnCore c with
  | none => rfl
  | some x => simp [Option.isEqSome]

/-- The self-switch case: when `tid` is already current, the conditional restore is
the identity (no register roll-back). -/
theorem restoreIncomingContextOnCoreUnlessCurrent_self (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (h : st.scheduler.currentOnCore c = some tid) :
    restoreIncomingContextOnCoreUnlessCurrent st c tid = st := by
  unfold restoreIncomingContextOnCoreUnlessCurrent; rw [if_pos (by simp [h])]

/-- The non-self-switch case: the conditional restore coincides with the plain
restore. -/
theorem restoreIncomingContextOnCoreUnlessCurrent_of_ne (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (h : st.scheduler.currentOnCore c ≠ some tid) :
    restoreIncomingContextOnCoreUnlessCurrent st c tid = restoreIncomingContextOnCore st c tid := by
  unfold restoreIncomingContextOnCoreUnlessCurrent
  rw [if_neg (by simp only [beq_iff_eq]; exact h)]

@[simp] theorem restoreIncomingContextOnCoreUnlessCurrent_scheduler (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    (restoreIncomingContextOnCoreUnlessCurrent st c tid).scheduler = st.scheduler := by
  unfold restoreIncomingContextOnCoreUnlessCurrent; split
  · rfl
  · exact restoreIncomingContextOnCore_scheduler st c tid

@[simp] theorem restoreIncomingContextOnCoreUnlessCurrent_objects (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    (restoreIncomingContextOnCoreUnlessCurrent st c tid).objects = st.objects := by
  unfold restoreIncomingContextOnCoreUnlessCurrent; split
  · rfl
  · exact restoreIncomingContextOnCore_objects st c tid

theorem restoreIncomingContextOnCoreUnlessCurrent_getTcb? (st : SystemState) (c : CoreId)
    (tid t : SeLe4n.ThreadId) :
    (restoreIncomingContextOnCoreUnlessCurrent st c tid).getTcb? t = st.getTcb? t := by
  unfold SystemState.getTcb?; rw [restoreIncomingContextOnCoreUnlessCurrent_objects]

@[simp] theorem restoreIncomingContextOnCoreUnlessCurrent_machine_timer (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    (restoreIncomingContextOnCoreUnlessCurrent st c tid).machine.timer = st.machine.timer := by
  unfold restoreIncomingContextOnCoreUnlessCurrent; split
  · rfl
  · exact restoreIncomingContextOnCore_machine_timer st c tid

theorem restoreIncomingContextOnCoreUnlessCurrent_regsOnCore_ne (st : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) (h : c ≠ c') :
    (restoreIncomingContextOnCoreUnlessCurrent st c tid).machine.regsOnCore c' = st.machine.regsOnCore c' := by
  unfold restoreIncomingContextOnCoreUnlessCurrent; split
  · rfl
  · exact restoreIncomingContextOnCore_regsOnCore_ne st c c' tid h

/-- Off the self-switch, the conditional restore sets core `c`'s bank to `tid`'s
saved context (as the plain restore does) — the contextMatches-establishment path. -/
theorem restoreIncomingContextOnCoreUnlessCurrent_regsOnCore_self_of_ne (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hNe : st.scheduler.currentOnCore c ≠ some tid) :
    (restoreIncomingContextOnCoreUnlessCurrent st c tid).machine.regsOnCore c = tcb.registerContext := by
  rw [restoreIncomingContextOnCoreUnlessCurrent_of_ne st c tid hNe]
  exact restoreIncomingContextOnCore_regsOnCore_self st c tid tcb hTcb

/-- Z4-D/E: For a system with all unbound threads, the effective selection
reduces to the original selection. -/
theorem chooseBestRunnableEffective_unbound_equiv
    (st : SystemState)
    (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (hAllUnbound : ∀ tid ∈ runnable, ∀ tcb : TCB,
      st.getTcb? tid = some tcb →
      tcb.schedContextBinding = .unbound ∧ tcb.pipBoost = none) :
    chooseBestRunnableEffective st eligible runnable best =
    chooseBestRunnableBy st.getObject? eligible runnable best := by
  induction runnable generalizing best with
  | nil => simp [chooseBestRunnableEffective, chooseBestRunnableBy]
  | cons tid rest ih =>
    simp only [chooseBestRunnableEffective, chooseBestRunnableBy]
    have hRest : ∀ t ∈ rest, ∀ tcb : TCB,
        st.getTcb? t = some tcb →
        tcb.schedContextBinding = .unbound ∧ tcb.pipBoost = none :=
      fun t hMemRest => hAllUnbound t (List.mem_cons_of_mem _ hMemRest)
    -- The two sides scrutinise different accessors — `getTcb?` on the left,
    -- `getObject?` on the right — so the split is taken on the kind-agnostic
    -- one and the typed reading is derived from it.  `getTcb?_eq_some_iff` is
    -- what relates them, and the `_ => ` arms are where they agree by both
    -- answering "not a TCB here".
    cases hObj : st.getObject? tid.toObjId with
    | none =>
      have hT : st.getTcb? tid = none := by
        unfold SeLe4n.Model.SystemState.getTcb?
        rw [show st.objects[tid.toObjId]? = none from hObj]
      rw [hT]; exact ih best hRest
    | some obj =>
      cases obj with
      | tcb tcb =>
        have hT : st.getTcb? tid = some tcb :=
          (SeLe4n.Model.SystemState.getTcb?_eq_some_iff st tid tcb).mpr hObj
        have hMem : tid ∈ tid :: rest := List.mem_cons_self ..
        have ⟨hUnb, hNoPip⟩ := hAllUnbound tid hMem tcb hT
        rw [hT]
        simp [hasSufficientBudget_unbound st tcb hUnb, Bool.and_true,
              resolveEffectivePrioDeadline, hUnb, hNoPip]
        apply ih
        intro t hMemRest
        exact hAllUnbound t (List.mem_cons_of_mem _ hMemRest)
      | _ =>
        all_goals (
          first
          | (have hT : st.getTcb? tid = none := by
               unfold SeLe4n.Model.SystemState.getTcb?
               rw [show st.objects[tid.toObjId]? = _ from hObj]
             rw [hT]; exact ih best hRest))

-- ============================================================================
-- WS-SM SM5.B — Per-core context switch (`switchToThreadOnCore`)
-- ============================================================================
--
-- The per-core analogue of seL4's `switchToThread`: dispatch a chosen thread
-- `tid` on a specific core `c`.  Unlike the read-only `chooseThreadOnCore`
-- (SM5.A), this is a state *transition* (it mutates the run queue, the current
-- thread, and the machine register file), so its definition lives here in the
-- production `Selection.lean` module alongside the other switch primitives
-- (`saveOutgoingContext` / `restoreIncomingContext`).
--
-- The forward-looking SM5.B theorems (sets-current, preempts-previous,
-- rejects-remote, run-queue-excludes-current, cross-core independence,
-- lock-set, totality, decidability) live in the staged module
-- `Scheduler.Operations.PerCoreSwitchToThread`, mirroring how SM5.A split the
-- production `chooseThreadOnCore` (here) from its staged theorem collection
-- (`PerCoreChooseThread`).  SM5.C's cross-core wake / SGI handler is the first
-- runtime exerciser.

/-- WS-SM SM5.B.4: does core `c` admit running `tcb`?

A thread with no CPU affinity (`cpuAffinity = none`) is *unbound* and admitted
on any core; a thread bound to `some c'` only on `c'`.  An unbound thread is homed
on the boot core (`determineTargetCore`), and the placement invariant
(`currentDequeuedUnique`, WS-ZA ZA6.3) keeps it there, so the gate's wider
admission is never what places it.  This is the predicate
`switchToThreadOnCore` consults for its reject-remote gate (Theorem 3.2.3): a
switch onto a core the thread is not admitted on is rejected with
`KernelError.threadOnDifferentCore` rather than silently migrating the thread. -/
def affinityAdmitsCore (tcb : TCB) (c : SeLe4n.Kernel.Concurrency.CoreId) : Bool :=
  match tcb.cpuAffinity with
  | none    => true
  | some c' => c' == c

/-- WS-SM SM5.B.4: an unbound thread (`cpuAffinity = none`) is admitted on
every core. -/
@[simp] theorem affinityAdmitsCore_none (tcb : TCB) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (h : tcb.cpuAffinity = none) : affinityAdmitsCore tcb c = true := by
  simp [affinityAdmitsCore, h]

/-- WS-SM SM5.B.4: a thread bound to `some c'` is admitted on core `c` iff
`c' = c`. -/
theorem affinityAdmitsCore_some (tcb : TCB) (c c' : SeLe4n.Kernel.Concurrency.CoreId)
    (h : tcb.cpuAffinity = some c') : affinityAdmitsCore tcb c = (c' == c) := by
  simp [affinityAdmitsCore, h]

/-- WS-SM SM5.B.3 (plan §3.2, Theorem 3.2.2): preempt core `c`'s current
thread in favour of an `incoming` thread.

Saves the outgoing thread's machine registers into its TCB `registerContext`
(so the preempted thread resumes exactly where it left off) and re-enqueues it
into core `c`'s run queue at its effective priority (`TCB.boostedPriority`,
i.e. `max(base, pipBoost)` — the priority every other re-enqueue site uses).
This is the "preempted thread goes back to the run queue" discipline.

No-op in three cases:
- core `c` has no current thread (`currentOnCore c = none`);
- the current thread *is* `incoming` (switching to the already-running thread —
  nothing to preempt);
- the current thread fails to resolve to a TCB (unreachable under
  `currentThreadValid`; fail-safe identity rather than corrupting state).

Only core `c`'s run-queue slot and the outgoing TCB are written; every other
core's scheduler slot is untouched (the cross-core-independence frame,
SM5.B.6). -/
def preemptCurrentOnCore (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (incoming : SeLe4n.ThreadId) : SystemState :=
  match st.scheduler.currentOnCore c with
  | none => st
  | some prevTid =>
    if prevTid == incoming then st
    else
      match st.getTcbWitnessed? prevTid with
      | some ⟨prevTcb, h⟩ =>
        -- The context save is an in-place rewrite (the lookup is its witness);
        -- the re-enqueue then writes the thread's run-queue links in its TCB
        -- (WS-ZA ZA4.5, `runEnqueueOnCore`).
        (st.rewriteObject prevTid.toObjId
            (.tcb { prevTcb with registerContext := st.machine.regsOnCore c })
            (SystemState.rewriteAdmissible_tcb h _)).runEnqueueOnCore c prevTid
          prevTcb.boostedPriority
      | none => st

/-- WS-ZA ZA5.2: **the compiled preemption.**  The core's words are written
into the file the outgoing TCB already owns (`RegisterFile.overwriteWith`),
read off the machine before the store is written, and the TCB is rewritten in
its slot (`updateTcb`), as `saveOutgoingContextOnCoreImpl` does: a TCB rebuilt
from the copy the lookup returned was a fresh 41-field record, and a file the
TCB and the core's bank both held was copied by the incoming thread's restore.
Proven equal (`preemptCurrentOnCore_eq_impl`). -/
def preemptCurrentOnCoreImpl (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (incoming : SeLe4n.ThreadId) : SystemState :=
  match st.scheduler.currentOnCore c with
  | none => st
  | some prevTid =>
    if prevTid == incoming then st
    else
      match st.getTcb? prevTid with
      | some prevTcb =>
        let regs := st.machine.regsOnCore c
        let prio := prevTcb.boostedPriority
        (st.updateTcb prevTid fun t =>
            { t with registerContext := SeLe4n.RegisterFile.overwriteWith regs t.registerContext }
          ).runEnqueueOnCore c prevTid prio
      | none => st

@[csimp] theorem preemptCurrentOnCore_eq_impl :
    @preemptCurrentOnCore = @preemptCurrentOnCoreImpl := by
  funext st c incoming
  unfold preemptCurrentOnCore preemptCurrentOnCoreImpl
  split
  · rfl
  · split
    · rfl
    · rename_i prevTid _ _
      split
      · next prevTcb hT _ =>
        simp only [hT, SeLe4n.RegisterFile.overwriteWith_eq]
        rw [SystemState.rewriteObject_tcb_eq_updateTcb hT
          (fun t => { t with registerContext := st.machine.regsOnCore c })]
      · next hN =>
        have hT : st.getTcb? prevTid = none := by
          cases hT : st.getTcb? prevTid with
          | none => rfl
          | some t => rw [SystemState.getTcbWitnessed?_eq_some hT] at hN; cases hN
        simp only [hT]

/-- WS-SM SM5.B.3 (frame): `preemptCurrentOnCore` never writes *any* core's
`current` slot — it only saves the outgoing thread's context (objects) and
re-enqueues it into core `c`'s run queue (scheduler).  So *every* core's
current thread is preserved.

**WS-RR RR7.36** moved this from the staged `PerCoreSwitchToThread` to sit
beside the transition it frames: `Operations/Core.lean`'s thread-state
preservation needs it and cannot import a staged module, and a second copy
there would be one question with two answers. -/
theorem preemptCurrentOnCore_currentOnCore (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (c' : CoreId) :
    (preemptCurrentOnCore st c incoming).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  unfold preemptCurrentOnCore
  split
  · rfl
  · split
    · rfl
    · split
      · simp [SystemState.rewriteObject_scheduler]
      · rfl

/-- `preemptCurrentOnCore` queues nothing on another core: it re-enqueues on its
own core only, and its context save keeps every run-queue core. -/
theorem preemptCurrentOnCore_queuedOn_ne (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (hInv : st.objects.invExt) (c' : CoreId) (h : c ≠ c')
    (y : SeLe4n.ThreadId) (hq : (preemptCurrentOnCore st c incoming).queuedOn c' y = true) :
    st.queuedOn c' y = true := by
  unfold preemptCurrentOnCore at hq
  split at hq
  · exact hq
  · split at hq
    · exact hq
    · split at hq
      · rename_i prevTid _ _ prevTcb hT _
        rw [SystemState.runEnqueueOnCore_queuedOn] at hq
        split at hq
        · exact absurd (of_decide_eq_true hq) (Ne.symm h)
        · rwa [(SystemState.RunCoresAgree.rewriteObject_tcb (tcb' := { prevTcb with registerContext := st.machine.regsOnCore c }) hT _ hInv rfl).queuedOn] at hq
      · exact hq

/-- WS-SM SM5.B.1 (plan §3.2): per-core context switch to `tid` on core `c`.

Performs, in order:
1. **Preempt** core `c`'s current thread (`preemptCurrentOnCore`): save its
   context + re-enqueue it (SM5.B.3 / Theorem 3.2.2).
2. **Dequeue** `tid` from core `c`'s run queue — dequeue-on-dispatch, matching
   seL4's `switchToThread` → `tcbSchedDequeue` (SM5.B.5: the new current thread
   is not simultaneously in the run queue).
3. **Restore** `tid`'s register context into the machine register file
   (`restoreIncomingContext`).
4. **Set** core `c`'s current thread to `tid` (SM5.B.1 / Theorem 3.2.1).

Failure modes are explicit (fail-closed `Except`):
- `tid` does not resolve to a TCB → `.schedulerInvariantViolation`.  A chosen
  thread must be a real TCB; a corrupted run-queue entry is surfaced, never
  silently dispatched (mirrors `chooseThreadOnCore`'s discipline).
- `tid`'s `cpuAffinity` binds it to a core `c' ≠ c` → `.threadOnDifferentCore`
  (SM5.B.4 / Theorem 3.2.3): cross-core migration is a separate explicit
  operation, never an implicit side effect of a context switch.

Returns the updated `SystemState` on success.  The single-state form (rather
than the `Kernel` monad) mirrors `chooseThreadOnCore`: SM5.C wraps it in the
per-core dispatch loop and the `withLockSet` acquisition over
`switchToThreadOnCoreLockSet` (the object-store + run-queue write locks).

**Relationship to `schedule` (deliberately distinct, not a missed
unification).**  `schedule`/`scheduleEffective` *drop* the outgoing thread —
under dequeue-on-dispatch the previous current was already removed from the run
queue when it was dispatched, so `schedule` does not re-enqueue it
(re-enqueue-on-preemption is the caller's job: `timerTick` / `handleYield` /
`switchDomain`).  `switchToThreadOnCore` is the higher-level *preemptive* switch:
it **does** re-enqueue the preempted thread (Theorem 3.2.2), as the SM5.C
cross-core wake / SGI handler requires when it preempts a running thread to
admit a higher-priority one.  Because the preempt-vs-drop semantics genuinely
differ, the two are *not* unified into one primitive (and there is no
`rfl`-bridge, unlike `chooseThread = chooseThreadOnCore bootCoreId`); they share
only the conceptual dequeue→restore→set-current tail.

**Per-core register model (SM4.B per-core banks).**  The abstract machine
carries a per-core register bank `MachineState.coreRegs : Vector RegisterFile
numCores` (accessor `regsOnCore c` / `setRegsOnCore c`);
`switchToThreadOnCore` restores `tid`'s context into **core `c`'s own bank**
(via `restoreIncomingContextOnCore c`), so the switch is correct for core `c`
without disturbing any sibling core's registers.  This is what makes
`contextMatchesCurrentOnCore` (which reads `regsOnCore c`) a genuine ∀-core
invariant: see `schedulerInvariantStructuralReg_smp` in
`Scheduler/Invariant/PerCoreInvariantSuite.lean`. -/
def switchToThreadOnCore (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) : Except KernelError SystemState :=
  match st.getTcb? tid with
  | some tidTcb =>
    if affinityAdmitsCore tidTcb c then
      let stPreempt := preemptCurrentOnCore st c tid
      let stDequeued := stPreempt.runRemoveOnCore c tid
      -- WS-SM SM5.B (PR #814 review P2-1, self-switch guard): restore `tid`'s
      -- context into core `c`'s bank UNLESS `tid` is already current — a running
      -- thread's live registers in `regsOnCore c` are authoritative, and
      -- restoring its (possibly stale) saved context would roll it back at the
      -- hardware/FFI boundary.  `stDequeued.currentOnCore c = st.currentOnCore c`
      -- (preempt + dequeue preserve `current`), so the helper detects the
      -- self-switch correctly.  The preempt no-ops (never re-enqueues the
      -- incoming thread), the dequeue no-ops for the current thread
      -- (dequeue-on-dispatch ⇒ not queued), and set-current is the identity, so a
      -- self-switch is observably a no-op.
      let stRestored := restoreIncomingContextOnCoreUnlessCurrent stDequeued c tid
      .ok { stRestored with scheduler := stRestored.scheduler.setCurrentOnCore c (some tid) }
    else
      .error .threadOnDifferentCore
  | none => .error .schedulerInvariantViolation

-- ============================================================================
-- WS-SM SM5.C — Cross-core wake via SGI (production transitions)
-- ============================================================================
--
-- The cross-core wake protocol (plan §3.3, §4.4): when a thread becomes
-- runnable, enqueue it on its *target* core (determined by its CPU affinity)
-- and — if that core is not the one currently executing the wake — emit a
-- `.reschedule` SGI so the target core re-runs its scheduler.  As with SM5.A's
-- `chooseThreadOnCore` and SM5.B's `switchToThreadOnCore`, the transitions live
-- here in production `Selection.lean`; the forward-looking SM5.C theorems
-- (lock-sets, wake / SGI / handler semantics, losslessness, the SGI delivery
-- latency bound, the affinity-control op) live in the staged module
-- `Scheduler.Operations.PerCoreWake`.  SM5.D's per-core timer tick is the first
-- runtime exerciser (the cross-core CBS-replenish wake at §3.4 calls `wakeThread`).

/-- WS-SM SM5.C.1 (audit-pass-3 / Codex-P2): is `tid` already runnable on *some*
core's run queue?  The global single-placement test the cross-core wake uses to
avoid a second placement of the same thread (which two SGI handlers could
otherwise dispatch concurrently).  Reads every per-core run queue via
`RunQueue.contains` over `Concurrency.allCores`. -/
def runnableOnSomeCore (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  (SeLe4n.Kernel.Concurrency.allCores).any
    (fun c => st.queuedOn c tid)

/-- WS-ZA ZA4.7: the compiled `runnableOnSomeCore`: the thread's run-core code
read once and compared with the core range, with no closure over the core list
and one lookup instead of one per core (`runnableOnSomeCore_eq_impl`). -/
@[inline] def runnableOnSomeCoreImpl (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? tid with
  | some tcb => tcb.runCoreCode != 0 && tcb.runCoreCode ≤ SeLe4n.Kernel.Concurrency.numCores
  | none => false

@[csimp] theorem runnableOnSomeCore_eq_impl :
    @runnableOnSomeCore = @runnableOnSomeCoreImpl := by
  funext st tid
  unfold runnableOnSomeCore runnableOnSomeCoreImpl
  cases h : st.objects[tid.toObjId]? with
  | none => simp [SystemState.queuedOn, SystemState.getTcb?, h]
  | some o =>
    cases o with
    | tcb tcb =>
      simp only [SystemState.queuedOn, SystemState.getTcb?, h]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq,
        decide_eq_true_eq]
      constructor
      · rintro ⟨c, _, hc⟩; rw [hc]; exact ⟨by omega, c.isLt⟩
      · rintro ⟨h0, hle⟩
        exact ⟨⟨tcb.runCoreCode - 1, by omega⟩, SeLe4n.Kernel.Concurrency.mem_allCores _,
          by simp only []; omega⟩
    | _ => simp [SystemState.queuedOn, SystemState.getTcb?, h]

/-- WS-SM SM5.D.4 (audit-pass-2 / Codex-P2): is `tid` the *current* (running)
thread on *some* core?  A running thread is dequeued-on-dispatch, so it is absent
from every run queue — `runnableOnSomeCore` (run-queue membership) does NOT catch
it.  The cross-core CBS-replenish wake (`processOneReplenishmentOnCore`) uses this
to suppress re-enqueueing a thread that is currently running on a *different* core
than its `determineTargetCore` (the deferred-affinity-migration case): without it,
the thread would be both current on the old core and runnable on the new — the same
TCB dispatchable on two cores.  Reads every per-core `currentOnCore` slot via
`Concurrency.allCores`. -/
def runningOnSomeCore (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  (SeLe4n.Kernel.Concurrency.allCores).any
    (fun c => st.scheduler.currentOnCore c == some tid)

/-- WS-ZA ZA5.2: whether a core runs a thread, asked of the core's
current-thread code, so no `some` cell is built for the comparison. -/
theorem currentOnCore_beq_some (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) :
    (st.scheduler.currentOnCore c == some tid) =
      (st.scheduler.currentCode.get c == tid.val + 1) := by
  simp only [SchedulerState.currentOnCore]
  cases st.scheduler.currentCode.get c with
  | zero => simp [SeLe4n.ThreadId.ofOptCode]
  | succ k =>
    simp only [SeLe4n.ThreadId.ofOptCode]
    obtain ⟨v⟩ := tid
    by_cases hk : k = v
    · subst hk; simp
    · rw [show (k + 1 == (⟨v⟩ : SeLe4n.ThreadId).val + 1) = false by simp [hk],
        beq_eq_false_iff_ne]
      intro h'; cases h'; exact hk rfl

/-- WS-ZA ZA5.2: `runningOnSomeCore` over a core list, each core's current-thread
code compared with the thread's, by recursion, so no predicate closure or `some`
cell is built (`runningOnSomeCore_eq_impl`). -/
def runningOnCoresImpl (st : SystemState) (tid : SeLe4n.ThreadId) :
    List SeLe4n.Kernel.Concurrency.CoreId → Bool
  | [] => false
  | c :: cs => st.scheduler.currentCode.get c == tid.val + 1 || runningOnCoresImpl st tid cs

/-- WS-ZA ZA5.2: the compiled `runningOnSomeCore`. -/
@[inline] def runningOnSomeCoreImpl (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  runningOnCoresImpl st tid SeLe4n.Kernel.Concurrency.allCores

@[csimp] theorem runningOnSomeCore_eq_impl : @runningOnSomeCore = @runningOnSomeCoreImpl := by
  funext st tid
  unfold runningOnSomeCore runningOnSomeCoreImpl
  induction SeLe4n.Kernel.Concurrency.allCores with
  | nil => rfl
  | cons c cs ih => rw [List.any_cons, runningOnCoresImpl, ← ih, currentOnCore_beq_some]

/-- **PR #895 review round 10: the core a thread is actually placed on.**

`runnableOnSomeCore` and `runningOnSomeCore` answer *whether* a thread is
placed; nothing answered **where**, so every caller needing the core reached for
a *proxy* — `determineExecutingCore`, which finds a core the thread is CURRENT
on and otherwise falls back to `bootCoreId`, or `determineTargetCore`, which
reads `cpuAffinity`.  Both are wrong for a removal:

* a thread queued but not current matches `determineExecutingCore` nowhere, so it
  resolves to the boot core and a deschedule there edits a queue the thread is
  not on;
* `determineTargetCore` names where the thread is homed, which is where it is
  placed only because the placement invariant (`currentDequeuedUnique`'s
  `currentHome` / `queuedHome`, WS-ZA ZA6.3) says so; a removal that read the home
  would be correct on committed states and wrong on any state that invariant is
  not yet known of, so the resolver reads the placement itself.

This is this project's *a proxy is not the fact* (PR #889 review round 23) at the
scheduler: the fact a removal is about is **queue membership**, and
`removeRunnableOnCore` acts on the run queue *and* the current slot of the core
it is handed, so the witness has to cover both.  `find?` over `allCores` in the
model's own core order makes the answer deterministic. -/
def placedCoreOf? (st : SystemState) (tid : SeLe4n.ThreadId) : Option CoreId :=
  (SeLe4n.Kernel.Concurrency.allCores).find?
    (fun c => st.queuedOn c tid
      || st.scheduler.currentOnCore c == some tid)

/-- `find?` succeeds exactly where `any` does.  Stated locally rather than
reached for by name so the resolver's tie-back below is elementary. -/
private theorem isSome_find?_eq_any {α : Type _} (p : α → Bool) :
    ∀ l : List α, (l.find? p).isSome = l.any p
  | [] => rfl
  | a :: t => by
      simp only [List.find?, List.any_cons]
      cases hp : p a with
      | true => simp
      | false => simpa [hp] using isSome_find?_eq_any p t

/-- The witness answers exactly when the predicate holds: `placedCoreOf?` is
`some` iff the thread is queued or running somewhere.  Stated so the resolver and
the two predicates cannot drift — the defect this resolver exists to close came
from a *second* answer to one question, and a third one would be the same
mistake. -/
theorem placedCoreOf?_isSome_iff (st : SystemState) (tid : SeLe4n.ThreadId) :
    (placedCoreOf? st tid).isSome
      = (runnableOnSomeCore st tid || runningOnSomeCore st tid) := by
  unfold placedCoreOf? runnableOnSomeCore runningOnSomeCore
  rw [isSome_find?_eq_any]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, (h1 | h2)⟩
    · exact Or.inl ⟨c, hc, h1⟩
    · exact Or.inr ⟨c, hc, h2⟩
  · rintro (⟨c, hc, h1⟩ | ⟨c, hc, h2⟩)
    · exact ⟨c, hc, Or.inl h1⟩
    · exact ⟨c, hc, Or.inr h2⟩

/-- A thread the resolver places on core `c` really is on `c` — queued or
running.  This is what licenses `removeRunnableOnCore` at that core. -/
theorem placedCoreOf?_sound (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (h : placedCoreOf? st tid = some c) :
    st.queuedOn c tid
      || st.scheduler.currentOnCore c == some tid := by
  simpa using List.find?_some h

/-- WS-ZA ZA4.5: does a wake on core `c` leave `tid` where it is?  It does when
the thread is already runnable on some core (the single-placement guard below),
or when its run-queue links do not admit `c` (`runEnqueueAdmits`: its links
already place it on another core's queue, seL4's `tcbQueued`).  Both are the
one test, so a wake either places the thread or changes nothing. -/
def wakeDeclines (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) : Bool :=
  runnableOnSomeCore st tid || !st.runEnqueueAdmits c tid

theorem wakeDeclines_eq_false_iff {st : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId} :
    wakeDeclines st c tid = false ↔
      runnableOnSomeCore st tid = false ∧ st.runEnqueueAdmits c tid = true := by
  unfold wakeDeclines
  cases runnableOnSomeCore st tid <;> cases st.runEnqueueAdmits c tid <;> simp

/-- Under the link agreement, a thread runnable on no core is admitted
everywhere, so a wake declines it only when it is already runnable. -/
theorem wakeDeclines_of_refined {st : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId}
    (hR : st.runQueueRefined) (hT : (st.getTcb? tid).isSome)
    (hF : runnableOnSomeCore st tid = false) (hI : isIdleThreadId tid = false) :
    wakeDeclines st c tid = false := by
  refine wakeDeclines_eq_false_iff.mpr ⟨hF, SystemState.runEnqueueAdmits_of_refined hR hT ?_ hI⟩
  intro c' _
  have hC := List.any_eq_false.mp hF c' (SeLe4n.Kernel.Concurrency.mem_allCores c')
  rw [← (hR c').queuedOn]
  simpa using hC

/-- WS-SM SM5.C.1 (plan §3.3): enqueue `tid` as a runnable thread on core `c`.

The per-core "make `tid` runnable on core `c`" primitive — the per-core
analogue of the IPC wake helper `IPC.ensureRunnable`, lifted to an explicit
`CoreId` and extended to also discharge the IPC↔scheduler coherence the
single-core helper assumed its caller had already established.

Concretely it (a) sets `tid`'s `ipcState := .ready` so the woken thread
satisfies `runnableThreadIpcReady` and is no longer flagged `blockedOn*` — the
exact field the per-core IPC↔scheduler invariants
(`runnableThreadIpcReady_perCore`, `blockedOn*NotRunnable_perCore`) gate
run-queue membership on (`threadState` is *not* gated by any run-queue
invariant, so it is left unchanged); and (b) inserts `tid` into core `c`'s run
queue at its effective priority (`TCB.boostedPriority`, i.e.
`max(base, pipBoost)` — the priority every other re-enqueue site uses).

**Single-placement guard (SM5.C.1 audit-pass-3 / Codex-P2).**  Before inserting,
the wake checks `runnableOnSomeCore`: if `tid` is ALREADY runnable on *some*
core's run queue, the wake is a no-op (identity).  This extends `RunQueue.insert`'s
per-core idempotency (its internal `contains` guard) to a *global* single-
placement invariant — a thread is runnable on at most one core — so a stale
placement (e.g. after an affinity change whose run-queue migration is deferred to
SM5.H.4) cannot leave the same TCB eligible on two cores, which two SGI handlers
could otherwise dispatch concurrently (the same thread running on two cores).
Fail-closed: a `tid` that does not resolve to a TCB is a no-op (identity),
mirroring `IPC.ensureRunnable`'s `none => st` discipline.

Footprint: WRITES core `c`'s run-queue slot and `tid`'s TCB — the TCB through
`SystemState.rewriteObject` under the witnessed lookup (`getTcbWitnessed?`), so
the wake's object-store write is one in-place table insert whose admissibility
proof is erased; the single-placement guard additionally READS every per-core
run queue.  `wakeThreadLockSet` declares
the write footprint; the guard's all-core read coverage is formalised when the
wake is wired under `withLockSet` at SM5.D (the lock set's runtime consumption is
SM5.D+).  Every other thread's TCB and every other core's `current` slot are
framed out (the cross-core-independence + per-thread frame lemmas in
`PerCoreWake`). -/
def enqueueRunnableOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcbWitnessed? tid with
  | some ⟨tcb, h⟩ =>
      -- WS-ZA ZA4.5: a thread its links already place on a queue is not
      -- placed again (`wakeDeclines`, seL4's `tcbQueued`).
      if wakeDeclines st c tid then st
      else
        -- WS-ZA ZA4.5: the insert writes the thread's run-queue links
        -- (`runEnqueueAdmitted`), after the `.ready` mark.
        let st' := (st.rewriteObject tid.toObjId (.tcb (tcb.setIpcState .ready))
            (SystemState.rewriteAdmissible_tcb h _)).runEnqueueAdmitted c tid tcb.boostedPriority
        -- The reschedule-SGI accumulator (KSC-1): a run-queue insert on `c`
        -- stales `c`'s decision (the diff's wake rule).
        { st' with scheduler := st'.scheduler.markReschedulePendingOnCore c }
  | none => st

/-- WS-ZA ZA4.7: the compiled `enqueueRunnableOnCore`.  The `.ready` mark is
written into the thread's own slot (`RHTable.modify`), with the priority read
first, so on an exclusively owned state the TCB is not copied
(`enqueueRunnableOnCore_eq_impl`). -/
def enqueueRunnableOnCoreImpl (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
      let prio := tcb.boostedPriority
      if wakeDeclines st c tid then st
      else
        let st' := (st.modifyObject tid.toObjId
          (SystemState.mapTcbObject fun t => (t.setIpcState .ready))).runEnqueueAdmitted c tid prio
        { st' with scheduler := st'.scheduler.markReschedulePendingOnCore c }
  | none => st

@[csimp] theorem enqueueRunnableOnCore_eq_impl :
    @enqueueRunnableOnCore = @enqueueRunnableOnCoreImpl := by
  funext st c tid
  unfold enqueueRunnableOnCore enqueueRunnableOnCoreImpl
  have hNone : (∀ t, st.objects[tid.toObjId]? ≠ some (.tcb t)) →
      st.getTcbWitnessed? tid = none := by
    intro hN
    unfold SystemState.getTcbWitnessed?
    split
    · next t hx => exact absurd hx (hN t)
    · rfl
  cases hx : st.objects[tid.toObjId]? with
  | none => rw [hNone (by intro t h; rw [hx] at h; cases h)]; simp only [SystemState.getTcb?, hx]
  | some o =>
    cases o with
    | tcb tcb =>
      rw [SystemState.getTcbWitnessed?_eq_some ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hx)]
      simp only [SystemState.getTcb?, hx]
      split
      · rfl
      · rw [SystemState.modifyObject, SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? hx]
        rfl
    | _ => rw [hNone (by intro t h; rw [hx] at h; cases h)]; simp only [SystemState.getTcb?, hx]

/-- WS-ZA ZA4.5: the enqueue writes only the object store (the `.ready` mark
and the woken thread's run-queue links) and the scheduler. -/
theorem enqueueRunnableOnCore_onlyObjectsSchedulerDiffer (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    (enqueueRunnableOnCore st c tid).onlyObjectsSchedulerDiffer st := by
  unfold enqueueRunnableOnCore
  split
  · split
    · exact .refl _
    · exact ((SystemState.runEnqueueAdmitted_onlyObjectsSchedulerDiffer _ c tid _).withScheduler
        _).trans rfl
  · exact .refl _

/-- WS-ZA ZA4.5: the enqueue keeps every core's run queue in agreement with
the threads' links: the `.ready` mark moves no link, the append is the proven
link append onto a thread no core holds, and the reschedule mark touches no
queue. -/
theorem enqueueRunnableOnCore_runQueueRefined {st : SystemState} (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hR : st.runQueueRefined) :
    (enqueueRunnableOnCore st c tid).runQueueRefined := by
  unfold enqueueRunnableOnCore
  split
  · rename_i tcb hT _
    split
    · exact hR
    · rename_i hNot
      have hAdm := (wakeDeclines_eq_false_iff.mp (by simpa using hNot)).2
      refine SystemState.runQueueRefined_of_frame (fun _ _ => rfl) rfl rfl ?_
      refine SystemState.runEnqueueAdmitted_refined
        (SystemState.rewriteObject_tcb_runQueueRefined _ hInv hT (fun _ => rfl) hR) ?_ ?_
      · rw [SystemState.rewriteObject_tcb_getTcb?_self _ _ _ _ hInv]; rfl
      · intro c' hne
        show (st.scheduler.runQueueOnCore c').contains tid = false
        exact SystemState.runEnqueueAdmits_not_contains hR hAdm c' hne
  · exact hR

/-- WS-ZA ZA4.5: the enqueue is the identity, or it inserts `tid` into core
`c`'s run queue (ghost queue and concrete ends) and marks `c` for rescheduling. -/
theorem enqueueRunnableOnCore_scheduler_cases (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    (enqueueRunnableOnCore st c tid).scheduler = st.scheduler ∨
      ∃ (E : RunQueueEnds) (p : SeLe4n.Priority),
        (enqueueRunnableOnCore st c tid).scheduler =
          ((st.scheduler.setRunQueueEndsOnCore c E).setRunQueueOnCore c
            ((st.scheduler.runQueueOnCore c).insert tid p)).markReschedulePendingOnCore c := by
  unfold enqueueRunnableOnCore
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr ⟨_, _, by simp only [SystemState.runEnqueueAdmitted_scheduler]; rfl⟩
  · exact Or.inl rfl

/-- SM6.D.2 micro-frame (cross-core): `enqueueRunnableOnCore` only *adds* `tid`
to core `c`'s run queue — it never removes any thread from any core's queue.
So every pre-state run-queue member is preserved. -/
theorem enqueueRunnableOnCore_mem_old (st : SystemState) (c c' : CoreId)
    (tid x : SeLe4n.ThreadId)
    (hMem : x ∈ st.scheduler.runQueueOnCore c') :
    x ∈ (enqueueRunnableOnCore st c tid).scheduler.runQueueOnCore c' := by
  rcases enqueueRunnableOnCore_scheduler_cases st c tid with h | ⟨E, p, h⟩ <;> rw [h]
  · exact hMem
  · rw [SchedulerState.markReschedulePendingOnCore_runQueueOnCore]
    by_cases hcc : c' = c
    · subst hcc
      rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
      exact (RunQueue.mem_insert _ _ _ _).mpr (Or.inl hMem)
    · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hcc),
        SchedulerState.setRunQueueEndsOnCore_runQueueOnCore]
      exact hMem

/-- WS-ZA ZA4.5: the wake moves no thread's run-queue membership but the woken
one's, which it puts on `c` when it does not decline. -/
theorem enqueueRunnableOnCore_queuedOn (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (c' : CoreId) (y : SeLe4n.ThreadId) :
    (enqueueRunnableOnCore st c tid).queuedOn c' y =
      if y = tid ∧ (st.getTcb? tid).isSome ∧ wakeDeclines st c tid = false then decide (c' = c)
      else st.queuedOn c' y := by
  cases hT : st.getTcb? tid with
  | none =>
    have hW : st.getTcbWitnessed? tid = none := by
      unfold SystemState.getTcbWitnessed?; split <;> simp_all [SystemState.getTcb?]
    simp only [enqueueRunnableOnCore, hW, Option.isSome_none, Bool.false_eq_true, false_and,
      and_false, if_false]
  | some tcb =>
    simp only [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hT,
      Option.isSome_some, true_and]
    cases hD : wakeDeclines st c tid
    · simp only [Bool.false_eq_true, if_false, and_true]
      show (SystemState.runEnqueueAdmitted _ c tid _).queuedOn c' y = _
      rw [SystemState.runEnqueueAdmitted_queuedOn,
        SystemState.rewriteObject_tcb_getTcb?_self _ _ _ _ hInv]
      by_cases hy : y = tid
      · rw [if_pos hy, if_pos hy]; rfl
      · rw [if_neg hy, if_neg hy]
        apply SystemState.queuedOn_of_getTcb?
        have hNe : ¬ (tid.toObjId == y.toObjId) = true :=
          fun hh => hy (SeLe4n.ThreadId.toObjId_injective _ _ (eq_of_beq hh)).symm
        simp only [SystemState.rewriteObject, SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId y.toObjId _ hNe hInv]
    · rw [if_pos rfl, if_neg (fun h => Bool.noConfusion h.2)]

/-- WS-ZA ZA4.5: on a thread that resolves to a TCB and is not yet runnable, the
enqueue inserts it into core `c`'s run queue at its boosted priority. -/
theorem enqueueRunnableOnCore_scheduler_of_fresh (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hFresh : wakeDeclines st c tid = false) :
    ∃ E : RunQueueEnds, (enqueueRunnableOnCore st c tid).scheduler =
      ((st.scheduler.setRunQueueEndsOnCore c E).setRunQueueOnCore c
        ((st.scheduler.runQueueOnCore c).insert tid tcb.boostedPriority)).markReschedulePendingOnCore c := by
  simp only [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hTcb, hFresh,
    Bool.false_eq_true, if_false]
  exact ⟨_, by simp only [SystemState.runEnqueueAdmitted_scheduler]; rfl⟩

/-- WS-ZA ZA4.5: on a thread that resolves to a TCB and is not yet runnable, the
enqueue's object store is the `.ready` mark — one insert at the thread's key —
up to TCB run-queue fields (the enqueue also writes the thread's and its
neighbours' run-queue links). -/
theorem enqueueRunnableOnCore_objectsAgree_marked (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hFresh : wakeDeclines st c tid = false) :
    (enqueueRunnableOnCore st c tid).objectsAgreeOffRunLinks
      { st with objects := st.objects.insert tid.toObjId (.tcb (tcb.setIpcState .ready)) } := by
  simp only [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hTcb, hFresh,
    Bool.false_eq_true, if_false]
  exact SystemState.objectsAgreeOffRunLinks.congr rfl rfl
    (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ c tid _)

/-- WS-SM SM5.C.1 (preservation): `enqueueRunnableOnCore` preserves the
RobinHood object-store invariant.  Its object-store writes are the woken
thread's `ipcState := .ready` save (an `insert` at an existing key) and the
run-queue link writes (in-place rewrites of resident TCBs), each of which
preserves `invExt`; the non-TCB branch is the identity. -/
theorem enqueueRunnableOnCore_preserves_objects_invExt (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (enqueueRunnableOnCore st c tid).objects.invExt := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_none hTcb]; exact hInv
  | some tcb =>
      simp only [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hTcb]
      split
      · exact hInv
      · exact SystemState.runEnqueueAdmitted_objects_invExt _ c tid _
          (SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt st.objects _ _ hInv)

/-- WS-ZA ZA4.5: the enqueue keeps the object store's kernel-level table
invariant — the `.ready` mark is an insert at a resident key and the link
writes rewrite resident values. -/
theorem enqueueRunnableOnCore_objects_invExtK (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hK : st.objects.invExtK) :
    (enqueueRunnableOnCore st c tid).objects.invExtK := by
  unfold enqueueRunnableOnCore
  split
  · split
    · exact hK
    · exact SystemState.runEnqueueAdmitted_objects_invExtK _ c tid _
        (SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExtK _ _ _ hK)
  · exact hK

/-- **WS-RR RR8.16** (`v0.35.199`): the enqueue is a `kindPreservingWrite` — its
one object write is the `rewriteObject` that marks the woken thread `.ready`, at
a key the enqueue has already resolved to a TCB.

The shape register row 85's two bundle frames consume; the wake lifts it through
`wakeThread_state_eq_enqueue`. -/
theorem enqueueRunnableOnCore_kindPreservingWrite (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    kindPreservingWrite st (enqueueRunnableOnCore st c tid) := by
  unfold enqueueRunnableOnCore
  cases hT : st.getTcbWitnessed? tid with
  | none => exact kindPreservingWrite.refl _
  | some p =>
    obtain ⟨tcb, hw⟩ := p
    simp only
    split
    · exact kindPreservingWrite.refl _
    · exact (SystemState.rewriteObject_tcb_kindPreservingWrite hw _ hInv
        (by exact ⟨rfl, rfl, rfl⟩)).trans
        (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ c tid _).kindPreserving

/-- The enqueue keeps the lifecycle metadata's consistency with the object
store: it writes no metadata, and every object it writes keeps its kind. -/
theorem enqueueRunnableOnCore_preserves_objectTypeMetadataConsistent (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (h : SystemState.objectTypeMetadataConsistent st) :
    SystemState.objectTypeMetadataConsistent (enqueueRunnableOnCore st c tid) := by
  intro oid
  have hL : SystemState.lookupObjectTypeMeta (enqueueRunnableOnCore st c tid) oid =
      SystemState.lookupObjectTypeMeta st oid := by
    have hD := enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c tid
    unfold SystemState.onlyObjectsSchedulerDiffer at hD
    rw [hD]; rfl
  rw [hL, h oid]
  rcases enqueueRunnableOnCore_kindPreservingWrite st c tid hInv oid with e | ⟨pre, post, h1, h2, h3, _⟩
  · rw [e]
  · rw [h1, h2]; simp only [Option.map_some, h3]

/-- **WS-RR RR8.16** (`v0.35.199`): ...and it writes neither CDT table — the
enqueue's two writes are one object and one run-queue slot. -/
theorem enqueueRunnableOnCore_cdt (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    (enqueueRunnableOnCore st c tid).cdt = st.cdt := by
  have h := enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c tid
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

/-- WS-SM SM5.I: `enqueueRunnableOnCore` leaves every core's replenish-queue slot
unchanged — it writes only objects (`ipcState := .ready`) and a run queue.

Declared in the **staged** `Scheduler/Operations/PerCoreTickCbsPreservation.lean`
until `v0.35.167`, where production could not read it: the live `.tcbResume`
arm's scheduler-domain footprint needs exactly this to declare an empty replenish
segment.  Moved beside the definition it frames. -/
theorem enqueueRunnableOnCore_replenishQueueOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueRunnableOnCore st c tid).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  rcases enqueueRunnableOnCore_scheduler_cases st c tid with h | ⟨E, p, h⟩ <;> rw [h]
  simp only [SchedulerState.markReschedulePendingOnCore_replenishQueueOnCore,
    SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
    SchedulerState.setRunQueueEndsOnCore_replenishQueueOnCore]

@[simp] theorem enqueueRunnableOnCore_releaseSlots (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    (enqueueRunnableOnCore st c tid).scheduler.releaseSlots = st.scheduler.releaseSlots := by
  rcases enqueueRunnableOnCore_scheduler_cases st c tid with h | ⟨E, p, h⟩ <;> rw [h] <;> rfl

/-- WS-ZA ZA6.3: the wake holds the release queues — it marks a thread ready
and links it into a run queue. -/
theorem enqueueRunnableOnCore_releaseStateAgree (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SystemState.releaseStateAgree (enqueueRunnableOnCore st c tid) st := by
  cases hT : st.getTcb? tid with
  | none =>
    simp only [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_none hT]
    exact .refl st
  | some tcb =>
    cases hD : wakeDeclines st c tid with
    | true =>
      simp only [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hT, hD, if_true]
      exact .refl st
    | false =>
      have hPre := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hT
      let st1 : SystemState :=
        { st with objects := st.objects.insert tid.toObjId (.tcb (tcb.setIpcState .ready)) }
      have a1 : SystemState.releaseStateAgree st1 st :=
        ⟨.insert hInv rfl (fun _ => by rw [hPre]; rfl), rfl⟩
      refine (SystemState.releaseStateAgree.of_agreeOffRunLinks (st := st1)
        (enqueueRunnableOnCore_objectsAgree_marked st c tid tcb hT hD) ?_).trans a1
      rcases enqueueRunnableOnCore_scheduler_cases st c tid with h | ⟨E, p, h⟩ <;> rw [h] <;> rfl

/-- WS-ZA ZA6.4: the wake keeps every context's refill view: it writes the
woken thread's state and run-queue links, no context. -/
theorem enqueueRunnableOnCore_refillViewsKept (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    RefillViewsKept (enqueueRunnableOnCore st c tid) st := by
  cases hT : st.getTcb? tid with
  | none =>
    simp only [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_none hT]
    exact .refl st
  | some tcb =>
    cases hD : wakeDeclines st c tid with
    | true =>
      simp only [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hT, hD, if_true]
      exact .refl st
    | false =>
      have hPre := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hT
      let st1 : SystemState :=
        { st with objects := st.objects.insert tid.toObjId (.tcb (tcb.setIpcState .ready)) }
      have a1 : RefillViewsKept st1 st := .insert hInv rfl (by rw [hPre]; rfl)
      exact (RefillViewsKept.of_agreeOffRunLinks (st := st1)
        (enqueueRunnableOnCore_objectsAgree_marked st c tid tcb hT hD)).trans a1

/-- WS-ZA ZA6.6: the wake keeps every yield code: it writes the woken thread's
state and run-queue links, no context. -/
theorem enqueueRunnableOnCore_yieldLinksKept (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    YieldLinksKept (enqueueRunnableOnCore st c tid) st := by
  cases hT : st.getTcb? tid with
  | none =>
    simp only [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_none hT]
    exact .refl st
  | some tcb =>
    cases hD : wakeDeclines st c tid with
    | true =>
      simp only [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hT, hD, if_true]
      exact .refl st
    | false =>
      have hPre := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hT
      let st1 : SystemState :=
        { st with objects := st.objects.insert tid.toObjId (.tcb (tcb.setIpcState .ready)) }
      have a1 : YieldLinksKept st1 st := .insert hInv rfl (by rw [hPre]; rfl)
      exact (YieldLinksKept.of_agreeOffRunLinks (st := st1)
        (enqueueRunnableOnCore_objectsAgree_marked st c tid tcb hT hD)).trans a1

/-- WS-SM SM5.C.2/.9 (plan §3.3): the core a thread is woken onto.

A thread bound to `some c'` (`cpuAffinity = some c'`) wakes onto `c'`; an
*unbound* thread (`cpuAffinity = none`, the TCB field default) wakes onto the
boot core (`bootCoreId`) — this is the SM5.C.9 "boot-time default affinity =
`bootCoreId`" rule, realised as the default *wake target* rather than by
mutating the field (keeping the trace byte-identical).  It is the thread's home:
the placement invariant (`currentDequeuedUnique`, WS-ZA ZA6.3) keeps every thread
current or queued only on the core this names, as seL4 keeps a thread on its
`tcbAffinity` core, although `affinityAdmitsCore` alone admits an unbound thread
on any core.  A `tid` that does not resolve to a TCB also defaults to `bootCoreId`
(fail-safe).

Pure function of `(st, tid)`; deterministic; total (`CoreId` is inhabited by
`bootCoreId`). -/
def determineTargetCore (st : SystemState) (tid : SeLe4n.ThreadId) : CoreId :=
  match st.getTcb? tid with
  | some tcb =>
      match tcb.cpuAffinity with
      | some c' => c'
      | none    => bootCoreId
  | none => bootCoreId

/-- WS-ZA ZA6.3: a thread is homed on the core `determineTargetCore` names. -/
theorem homedOn_determineTargetCore (st : SystemState) (tid : SeLe4n.ThreadId) :
    st.homedOn tid (determineTargetCore st tid) := fun x hx => by
  unfold determineTargetCore; simp only [hx]; cases hA : x.cpuAffinity <;> simp

/-- WS-ZA ZA6.3: ...and a thread with a TCB homed on `c` has `c` for its
`determineTargetCore`. -/
theorem determineTargetCore_eq_of_homedOn {st : SystemState} {tid : SeLe4n.ThreadId}
    {c : CoreId} {x : TCB} (hx : st.getTcb? tid = some x) (h : st.homedOn tid c) :
    determineTargetCore st tid = c := by
  have := h x hx
  unfold determineTargetCore; rw [hx]; cases hA : x.cpuAffinity <;> simp_all

/-- WS-ZA ZA6.3: an active thread homed on `c` has `c` for its
`determineTargetCore`. -/
theorem determineTargetCore_eq_of_active_homedOn {st : SystemState} {tid : SeLe4n.ThreadId}
    {c : CoreId} (ha : st.activeAt tid) (h : st.homedOn tid c) :
    determineTargetCore st tid = c :=
  let ⟨_, hx, _⟩ := ha; determineTargetCore_eq_of_homedOn hx h

/-- WS-SM SM6.E (PR #831 review 4, P1): the core **actually running** `tid` —
the first core whose current slot holds it (`none` when not current anywhere).
`determineTargetCore` is the wake/queue *home* (affinity defaulting to boot).
On a committed state the two agree: an affinity change that moves a running
thread's home takes it off the core it ran on in the same transition
(`setThreadCpuAffinityWithMigration`'s vacate, WS-ZA ZA6.3), so the placement
invariant (`currentDequeuedUnique`'s `currentHome`) holds.  A suspend still
deschedules and pokes the core that is running the thread, read here, rather
than its home: the core it acts on is then the one whose slot it clears, whether
or not that invariant is known of the state it is handed.  Completeness of the
first-match scan rests on `currentThreadUniqueAcrossCores`
(`Scheduler/Invariant/PerCore.lean`, audit closure): a thread is current on
at most one core.

**Lives here, beside `determineTargetCore`, not in `Lifecycle/Suspend.lean`
(PR #861 review round 39) and no longer in `Scheduler/Operations/Core.lean`
(the reschedule-SGI accumulator, KSC-1).**  The unbind path needs it — its
preemption guard was keyed on `determineTargetCore` while the wrapper's
reschedule was keyed on this, and those diverge for exactly the case the
paragraph above describes — and so does `markKeyChangeFor`
(`Scheduler/Operations/ReschedulePending.lean`), which the priority-inheritance
writers call and which `Core.lean`'s import chain sits above; the two homes of a
thread's placement are answered side by side.  `Lifecycle.Suspend.runningCoreOf?`
remains a working name via an `export`, so every existing qualified reference
is unchanged. -/
def runningCoreOf? (st : SystemState) (tid : SeLe4n.ThreadId) : Option CoreId :=
  SeLe4n.Kernel.Concurrency.allCores.find? (fun c =>
    st.scheduler.currentOnCore c == some tid)

/-- WS-ZA ZA5.2: every core, each as the `some` the running-core search answers:
a closed list, so an answer drawn from it is never built. -/
def allCoresSome : List (Option CoreId) := SeLe4n.Kernel.Concurrency.allCores.map some

/-- WS-ZA ZA5.2: the running-core search over cores already wrapped in `some`,
each core's current-thread code compared with the thread's, so the answer is the
list's own cell and no closure is built (`runningCoreOf?_eq_impl`). -/
def runningCoreOfOver (st : SystemState) (tid : SeLe4n.ThreadId) :
    List (Option CoreId) → Option CoreId
  | [] => none
  | o :: os =>
    match o with
    | some c => if st.scheduler.currentCode.get c == tid.val + 1 then o
                else runningCoreOfOver st tid os
    | none => runningCoreOfOver st tid os

/-- WS-ZA ZA5.2: the compiled `runningCoreOf?`. -/
@[inline] def runningCoreOfImpl (st : SystemState) (tid : SeLe4n.ThreadId) : Option CoreId :=
  runningCoreOfOver st tid allCoresSome

@[csimp] theorem runningCoreOf?_eq_impl : @runningCoreOf? = @runningCoreOfImpl := by
  funext st tid
  unfold runningCoreOf? runningCoreOfImpl allCoresSome
  induction SeLe4n.Kernel.Concurrency.allCores with
  | nil => rfl
  | cons c cs ih =>
    rw [List.find?_cons, List.map_cons, runningCoreOfOver, currentOnCore_beq_some]
    cases hc : (st.scheduler.currentCode.get c == tid.val + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih
    · rfl

/-- WS-ZA ZA5.2: the placement search over cores already wrapped in `some`, each
core asked of the thread's own run-queue link and the core's current-thread
code, so the answer is the list's own cell and no closure is built
(`placedCoreOf?_eq_impl`). -/
def placedCoreOfOver (st : SystemState) (tid : SeLe4n.ThreadId) :
    List (Option CoreId) → Option CoreId
  | [] => none
  | o :: os =>
    match o with
    | some c => if st.queuedOn c tid || st.scheduler.currentCode.get c == tid.val + 1 then o
                else placedCoreOfOver st tid os
    | none => placedCoreOfOver st tid os

/-- WS-ZA ZA5.2: the compiled `placedCoreOf?`. -/
@[inline] def placedCoreOfImpl (st : SystemState) (tid : SeLe4n.ThreadId) : Option CoreId :=
  placedCoreOfOver st tid allCoresSome

@[csimp] theorem placedCoreOf?_eq_impl : @placedCoreOf? = @placedCoreOfImpl := by
  funext st tid
  unfold placedCoreOf? placedCoreOfImpl allCoresSome
  induction SeLe4n.Kernel.Concurrency.allCores with
  | nil => rfl
  | cons c cs ih =>
    rw [List.find?_cons, List.map_cons, placedCoreOfOver, currentOnCore_beq_some]
    cases hc : (st.queuedOn c tid || st.scheduler.currentCode.get c == tid.val + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih
    · rfl

/-- A thread no core runs is current on no core. -/
theorem runningCoreOf?_none_currentOnCore {st : SystemState} {tid : SeLe4n.ThreadId}
    (h : runningCoreOf? st tid = none) (c : CoreId) : st.scheduler.currentOnCore c ≠ some tid := by
  intro hc
  have := List.find?_eq_none.mp h c (SeLe4n.Kernel.Concurrency.mem_allCores c)
  simp [hc] at this

/-- The core `runningCoreOf?` names runs the thread. -/
theorem runningCoreOf?_some_currentOnCore {st : SystemState} {tid : SeLe4n.ThreadId} {r : CoreId}
    (h : runningCoreOf? st tid = some r) : st.scheduler.currentOnCore r = some tid := by
  simpa using List.find?_some h

/-- **WS-RR RR7.30**: the routing decision never names a PE the board does not
have.

`setThreadCpuAffinityWithMigration` refuses an affinity at or above
`machine.declaredCoreCount` and `bootAffinitiesDeclared` refuses a configured
one, so every *pinned* thread is already inside the declared set.  This is the
other half — the unpinned one — and it is the half nothing stated: a thread with
`cpuAffinity = none`, and a `tid` that resolves to no TCB at all, both route to
`bootCoreId`, which is core `0`, and every binding declares at least one PE
(`PlatformBinding.coreCountPos`, carried onto the machine by
`declaredCoreCountAgrees`).  Together with the two refusals, no thread is ever
enqueued on a core `chooseThreadOnCore` would find empty.

Stated against `machine.declaredCoreCount` rather than against a binding's
`coreCount` because that is what a kernel transition can read; the hypothesis is
the pinned invariant the two refusals maintain, supplied rather than assumed. -/
theorem determineTargetCore_lt_declaredCoreCount (st : SystemState)
    (tid : SeLe4n.ThreadId) (hPos : 0 < st.machine.declaredCoreCount)
    (hAff : ∀ tcb, st.getTcb? tid = some tcb →
        ∀ c, tcb.cpuAffinity = some c → c.val < st.machine.declaredCoreCount) :
    (determineTargetCore st tid).val < st.machine.declaredCoreCount := by
  unfold determineTargetCore
  cases hT : st.getTcb? tid with
  | none => simpa [bootCoreId] using hPos
  | some tcb =>
    cases hA : tcb.cpuAffinity with
    | none => simp only [hA]; simpa [bootCoreId] using hPos
    | some c => simp only [hA]; simpa using hAff tcb hT c hA

/-- WS-SM SM5.C.2 / WS-RR RR2.3: `determineTargetCore` depends on the thread only
through its TCB's `cpuAffinity` — two states whose `getTcb?` agree up to
`cpuAffinity` route the thread to the same core.  The congruence that lets a
wake's SGI target be read at the pre-state rather than at the post-store wake
site, and that lets the cross-core donation arms resolve the replenishment
migration's endpoints before the rebinding runs.

Lives here, beside the definition, since RR2.3: it used to sit in
`IPC/CrossCore/NotificationSignal.lean`, which the donation operations cannot
see, and a second copy of a four-line congruence is exactly the duplication this
project treats as debt. -/
theorem determineTargetCore_congr (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (h : (st'.getTcb? tid).map (·.cpuAffinity) = (st.getTcb? tid).map (·.cpuAffinity)) :
    determineTargetCore st' tid = determineTargetCore st tid := by
  cases hT' : st'.getTcb? tid with
  | none => cases hT : st.getTcb? tid with
    | none => simp [determineTargetCore, hT', hT]
    | some t => rw [hT', hT] at h; simp at h
  | some t' => cases hT : st.getTcb? tid with
    | none => rw [hT', hT] at h; simp at h
    | some t =>
      have hAff : t'.cpuAffinity = t.cpuAffinity := by rw [hT', hT] at h; simpa using h
      simp [determineTargetCore, hT', hT, hAff]

/-- WS-ZA ZA4.5: a step that writes only run-queue links moves no thread's home
core — `determineTargetCore` reads `cpuAffinity`, which is off the links. -/
theorem determineTargetCore_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffRunLinks st) (tid : SeLe4n.ThreadId) :
    determineTargetCore st' tid = determineTargetCore st tid :=
  determineTargetCore_congr st st' tid
    (TCB.map_proj_eq_of_map_withoutRunLinks_eq (·.cpuAffinity) (h.getTcb? tid))

-- ============================================================================
-- The placement primitives — a removal at a core, at a pre-resolved placement,
-- and at the placement the state resolves
-- ============================================================================
--
-- **Relocated from `IPC/CrossCore/EndpointCall.lean` at `v0.35.158`.**
-- `removeRunnableOnCore` (SM6.A.1) and the state-resolved `descheduleAt` /
-- `descheduleAtPlacement` (WS-RR RR8.6, PR #895 review round 10) were declared
-- in the IPC cross-core layer because the `.call` rendezvous was their first
-- consumer.  They are scheduler operations — a run queue and a current slot are
-- all they read or write — and the cancellation reclaim's holder deschedule
-- (`descheduleUnboundHolder`, `Lifecycle/Suspend.lean`) is an asker that layer
-- cannot reach: `Lifecycle/Suspend.lean` and `IPC/CrossCore/EndpointCall.lean`
-- both import this module and neither imports the other.  *When a question has
-- one owner and an asker that cannot see it, the owner is in the wrong layer.*
-- The definitions sit beside `placedCoreOf?`, the resolver the state-resolved
-- form is defined by, and beside `determineTargetCore_congr`, which their home
-- core frames consume.  The `SeLe4n.Kernel` namespace is unchanged, so nothing
-- in the tree is renamed; the bridge to the single-core `removeRunnable`
-- (`removeRunnableOnCore_bootCoreId`) stays in the IPC layer, which is the
-- first layer that can name both sides of it.

/-- WS-SM SM6.A.1 (plan §3.2 steps 5–6): the per-core generalisation of
`removeRunnable`. Removes `tid` from core `c`'s run queue and, if `tid` is
core `c`'s current thread, clears `c`'s current slot. Only core `c`'s
scheduler slots are touched; every other core is framed out.

The single-core `removeRunnable` (bootCore-pinned) is exactly the `bootCoreId`
instance — see `removeRunnableOnCore_bootCoreId`. -/
def removeRunnableOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    SystemState :=
  -- WS-ZA ZA4.5: the dequeue unlinks the thread's run-queue links in the TCBs.
  st.runDescheduleOnCore c tid

/-- WS-ZA ZA4.5: the dequeue writes only the object store (the run-queue links
of the dequeued thread and its neighbours) and the scheduler. -/
theorem removeRunnableOnCore_onlyObjectsSchedulerDiffer (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (removeRunnableOnCore st tid c).onlyObjectsSchedulerDiffer st :=
  SystemState.runDescheduleOnCore_onlyObjectsSchedulerDiffer st c tid

/-- WS-ZA ZA4.5: the dequeue changes no object off the run-queue links (was
`removeRunnableOnCore_preserves_objects` while the links lived in the
scheduler). -/
theorem removeRunnableOnCore_objectsAgreeOffRunLinks (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (removeRunnableOnCore st tid c).objectsAgreeOffRunLinks st :=
  SystemState.runDescheduleOnCore_objectsAgreeOffRunLinks st c tid

/-- WS-ZA ZA4.5: what the dequeue does to the scheduler — core `c`'s ghost
queue loses `tid`, its concrete ends are the unlinked ends, and its `current`
slot is cleared if `tid` held it. -/
theorem removeRunnableOnCore_scheduler (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) :
    (removeRunnableOnCore st tid c).scheduler =
      SchedulerState.markReschedulePendingOnCoreIf
        (((st.scheduler.setRunQueueEndsOnCore c (st.runRemoveEnds c tid)).setRunQueueOnCore c
          ((st.scheduler.runQueueOnCore c).remove tid)).setCurrentOnCore c
          (if (st.scheduler.currentOnCore c) = some tid then none
            else (st.scheduler.currentOnCore c)))
        c (st.scheduler.currentOnCore c == some tid) :=
  SystemState.runDescheduleOnCore_scheduler st c tid

theorem removeRunnableOnCore_objects_invExt (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (hInv : st.objects.invExt) :
    (removeRunnableOnCore st tid c).objects.invExt :=
  SystemState.runDescheduleOnCore_objects_invExt st c tid hInv

/-- **WS-RR RR8.6**: remove `tid` from a placement its caller has already
resolved — `descheduleAtPlacement`'s body, split out so a transition that must
declare its footprint *before* it runs can resolve the placement on the
pre-state and remove at it later, through the one primitive the state-resolved
form is defined by.  `suspendThreadOnCore` is that transition: its scheduler
footprint (`suspendThreadOnCoreLockSet`) is declared over `placedCoreOf?`
of the syscall's pre-state, and nothing between the resolution and this removal
moves a thread between scheduler slots — the IPC teardown and both donation
arms write no run queue and no current slot, and the priority-inheritance
revert re-buckets a chain member inside the queue it already sits in — so the
pre-resolved placement is the placement the removal finds.

A removal at `none` is the identity: a thread the state places nowhere is on no
scheduler slot to be taken off. -/
def descheduleAt (st : SystemState) (tid : SeLe4n.ThreadId) (placed : Option CoreId) :
    SystemState :=
  match placed with
  | some c => removeRunnableOnCore st tid c
  | none => st

/-- **Deschedule `tid` wherever it actually is.**

The one step for "take this thread off the scheduler", for the reason round 10
gave and then did not finish applying: `removeRunnableOnCore` accepts a core
from *anyone*, so protecting one named wrapper leaves every direct caller free
to hand it a proxy.  Round 10 removed the core parameter from
`replyRecvHolderDeschedule` and left its sibling arm calling the primitive
directly with `determineExecutingCore`'s answer, so the same defect survived
twenty-five lines away (PR #895 review round 11).

A caller that knows the core — the executing core of a syscall, a wake target
it just computed — still calls `removeRunnableOnCore` directly and should.  This
is for the other case: a thread *resolved from the state*, whose placement is a
fact to look up rather than a parameter to pass. -/
def descheduleAtPlacement (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  descheduleAt st tid (placedCoreOf? st tid)

/-- The cores `descheduleAtPlacement` may write, read off the SAME resolver the
step itself uses — so a footprint and its transition cannot name different
cores, which is the divergence round 10's cut introduced. -/
def descheduleAtPlacementCores (st : SystemState) (tid : SeLe4n.ThreadId) : List CoreId :=
  match placedCoreOf? st tid with
  | some c => [c]
  | none => []

/-- WS-ZA ZA4.5: the dequeue keeps the run queues in agreement with the links. -/
theorem removeRunnableOnCore_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) : SystemState.RunQueueStage st (removeRunnableOnCore st tid c) :=
  SystemState.RunQueueStage.runDescheduleOnCore st c tid

/-- ...and so does the removal at a resolved placement, on either arm. -/
theorem descheduleAt_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (placed : Option CoreId) : SystemState.RunQueueStage st (descheduleAt st tid placed) := by
  unfold descheduleAt
  cases placed with
  | none => exact SystemState.RunQueueStage.refl st
  | some c => exact removeRunnableOnCore_runQueueStage st tid c

/-- WS-RR RR2.9 (frame): descheduling a thread on a core writes that core's run
queue and current slot and nothing else — in particular **no** replenish queue.
The reply path's donation return composes the SM5.H replenishment migration with
this deschedule, so the affinity invariant the migration establishes has to
survive it. -/
@[simp] theorem removeRunnableOnCore_replenishQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c c' : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  simp [removeRunnableOnCore]

@[simp] theorem removeRunnableOnCore_releaseSlots (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.releaseSlots = st.scheduler.releaseSlots :=
  SystemState.runDescheduleOnCore_releaseSlots st c tid



/-- **WS-RR RR8.16** (`v0.35.200`): ...and not the derivation tree, for the same
reason.  Stated beside the object frame because the capability bundle reads
`cdt` exactly as it reads the store, and both IPC spines end in
this removal. -/
@[simp] theorem removeRunnableOnCore_cdt (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (removeRunnableOnCore st tid c).cdt = st.cdt := by
  have h := removeRunnableOnCore_onlyObjectsSchedulerDiffer st tid c
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

/-- The step writes no object off the run-queue links, at either branch
(WS-ZA ZA4.5; was an object-store equality while the links lived in the
scheduler). -/
theorem descheduleAtPlacement_objectsAgreeOffRunLinks (st : SystemState)
    (tid : SeLe4n.ThreadId) : (descheduleAtPlacement st tid).objectsAgreeOffRunLinks st := by
  unfold descheduleAtPlacement descheduleAt
  split
  · exact removeRunnableOnCore_objectsAgreeOffRunLinks _ _ _
  · exact .refl _

/-- ...and it writes only the object store and the scheduler. -/
theorem descheduleAtPlacement_onlyObjectsSchedulerDiffer (st : SystemState)
    (tid : SeLe4n.ThreadId) : (descheduleAtPlacement st tid).onlyObjectsSchedulerDiffer st := by
  unfold descheduleAtPlacement descheduleAt
  split
  · exact removeRunnableOnCore_onlyObjectsSchedulerDiffer _ _ _
  · rfl

/-- **WS-RR RR8.12 Cut C6e**: and so it keeps object-store integrity — the form
every consumer that hands a descheduled state to a step reading `invExt` wants.
Stated here rather than re-derived: it was spelled inline at three sites in
`Kernel/API.lean`, which is the duplication this project retires. -/
theorem descheduleAtPlacement_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (descheduleAtPlacement st tid).objects.invExt := by
  unfold descheduleAtPlacement descheduleAt
  split
  · exact removeRunnableOnCore_objects_invExt _ _ _ hInv
  · exact hInv

/-- ...and the derivation tree itself (`v0.35.199`). -/
@[simp] theorem descheduleAtPlacement_cdt (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (descheduleAtPlacement st tid).cdt = st.cdt := by
  have h := descheduleAtPlacement_onlyObjectsSchedulerDiffer st tid
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

/-- WS-RR RR8.11: ...and hence moves no thread's home core.  Stated beside the
object frame it is derived from, because the SM5.H replenish-affinity invariant
reads `determineTargetCore` at whichever thread a scheduling context is bound to
and the cancellation composite ends in this removal. -/
@[simp] theorem descheduleAtPlacement_determineTargetCore (st : SystemState)
    (tid x : SeLe4n.ThreadId) :
    determineTargetCore (descheduleAtPlacement st tid) x = determineTargetCore st x :=
  determineTargetCore_of_objectsAgreeOffRunLinks
    (descheduleAtPlacement_objectsAgreeOffRunLinks st tid) x


/-- **WS-RR RR8.12**: the bare removal moves no thread's home core either.

`removeRunnableOnCore` writes only `scheduler`, and `determineTargetCore` reads
`cpuAffinity` through the object store -- so a *pre-state* scheduler footprint
may name a core that a deschedule-shaped step later writes at, rather than
assuming the two coincide.  The sibling of
`descheduleAtPlacement_determineTargetCore` above, at the primitive that one
composes. -/
@[simp] theorem removeRunnableOnCore_determineTargetCore (st : SystemState)
    (tid x : SeLe4n.ThreadId) (c : CoreId) :
    determineTargetCore (removeRunnableOnCore st tid c) x = determineTargetCore st x :=
  determineTargetCore_of_objectsAgreeOffRunLinks
    (removeRunnableOnCore_objectsAgreeOffRunLinks st tid c) x


/-- `placedCoreOf?` reads each thread's run-queue core (from its TCB) and each
core's current slot, so a step that keeps every thread's run-queue core
(`RunCoresAgree`) and every current slot places every thread alike. -/
theorem placedCoreOf?_congr_of_runCores_current_eq {st st' : SystemState}
    (tid : SeLe4n.ThreadId) (hQ : SystemState.RunCoresAgree st' st)
    (h : ∀ c : CoreId, st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    placedCoreOf? st' tid = placedCoreOf? st tid := by
  unfold placedCoreOf?
  have hp : (fun c : CoreId => st'.queuedOn c tid
      || st'.scheduler.currentOnCore c == some tid)
      = (fun c : CoreId => st.queuedOn c tid
      || st.scheduler.currentOnCore c == some tid) := by
    funext c; rw [hQ.queuedOn c tid, h c]
  rw [hp]

/-- ...and the core list it produces moves with it. -/
theorem descheduleAtPlacementCores_congr_of_runCores_current_eq {st st' : SystemState}
    (tid : SeLe4n.ThreadId) (hQ : SystemState.RunCoresAgree st' st)
    (h : ∀ c : CoreId, st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    descheduleAtPlacementCores st' tid = descheduleAtPlacementCores st tid := by
  unfold descheduleAtPlacementCores
  rw [placedCoreOf?_congr_of_runCores_current_eq tid hQ h]

/-- The core list is the resolver's answer as a list — the shape a pre-resolved
removal's write set (`descheduleAt … placed`, confined to `placed.toList`) is
stated in, so the two spellings of "the cores a placement removal writes" are
one fact rather than two definitions a reader must compare. -/
theorem descheduleAtPlacementCores_eq_toList (st : SystemState) (tid : SeLe4n.ThreadId) :
    descheduleAtPlacementCores st tid = (placedCoreOf? st tid).toList := by
  unfold descheduleAtPlacementCores
  cases placedCoreOf? st tid <;> rfl

/-- A thread placed on exactly one core — queued or current on `w`, and on no
other core — is placed there by the resolver.  The `find?` takes the first
satisfying core, and with one candidate there is no other to take. -/
theorem placedCoreOf?_eq_some_of_unique (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : CoreId)
    (hw : (st.queuedOn w tid
      || st.scheduler.currentOnCore w == some tid) = true)
    (hOther : ∀ c : CoreId, c ≠ w →
      (st.queuedOn c tid
        || st.scheduler.currentOnCore c == some tid) = false) :
    placedCoreOf? st tid = some w := by
  cases hp : placedCoreOf? st tid with
  | none =>
    have hIs := placedCoreOf?_isSome_iff st tid
    rw [hp, Option.isSome_none] at hIs
    have hAny : (runnableOnSomeCore st tid || runningOnSomeCore st tid) = true := by
      unfold runnableOnSomeCore runningOnSomeCore
      rcases Bool.or_eq_true_iff.mp hw with h1 | h2
      · exact Bool.or_eq_true_iff.mpr (Or.inl
          (List.any_eq_true.mpr ⟨w, SeLe4n.Kernel.Concurrency.mem_allCores w, h1⟩))
      · exact Bool.or_eq_true_iff.mpr (Or.inr
          (List.any_eq_true.mpr ⟨w, SeLe4n.Kernel.Concurrency.mem_allCores w, h2⟩))
    rw [hAny] at hIs
    exact absurd hIs Bool.false_ne_true
  | some x =>
    have hx := placedCoreOf?_sound st tid x hp
    by_cases hxw : x = w
    · rw [hxw]
    · rw [hOther x hxw] at hx
      exact absurd hx Bool.false_ne_true

/-- ...and never advances the machine timer, at either branch (`v0.35.37`).  The
reply path's donation return composes this step, and its `machine` frame reaches
back to the return through it. -/
@[simp] theorem descheduleAtPlacement_machine_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) : (descheduleAtPlacement st tid).machine = st.machine := by
  have h := descheduleAtPlacement_onlyObjectsSchedulerDiffer st tid
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

/-- ...and no replenish queue, at either branch.  All three facts are proved HERE
rather than at each consumer: a caller that re-derives them per core is how the
`serverCore` parameter got threaded into three proofs and one of them kept it
after the transition stopped using it. -/
@[simp] theorem descheduleAtPlacement_replenishQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (descheduleAtPlacement st tid).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold descheduleAtPlacement descheduleAt
  split
  · exact removeRunnableOnCore_replenishQueueOnCore _ _ _ _
  · rfl

@[simp] theorem descheduleAtPlacement_releaseSlots (st : SystemState) (tid : SeLe4n.ThreadId) :
    (descheduleAtPlacement st tid).scheduler.releaseSlots = st.scheduler.releaseSlots := by
  unfold descheduleAtPlacement descheduleAt
  split
  · exact removeRunnableOnCore_releaseSlots _ _ _
  · rfl

/-- `removeRunnableOnCore` preserves every `getTcb?` lookup off the run-queue
links (WS-ZA ZA4.5). -/
theorem removeRunnableOnCore_getTcb? (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (x : SeLe4n.ThreadId) :
    ((removeRunnableOnCore st tid c).getTcb? x).map TCB.withoutRunLinks
      = (st.getTcb? x).map TCB.withoutRunLinks :=
  (removeRunnableOnCore_objectsAgreeOffRunLinks st tid c).getTcb? x

/-- `removeRunnableOnCore` writes core `c`'s run-queue slot to `remove tid`. -/
@[simp] theorem removeRunnableOnCore_runQueueOnCore_self (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.runQueueOnCore c
      = (st.scheduler.runQueueOnCore c).remove tid := by
  simp [removeRunnableOnCore]

/-- `removeRunnableOnCore` clears core `c`'s current slot when it held `tid`. -/
theorem removeRunnableOnCore_currentOnCore_self (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.currentOnCore c
      = if st.scheduler.currentOnCore c = some tid then none
        else st.scheduler.currentOnCore c := by
  simp [removeRunnableOnCore]

/-- After `removeRunnableOnCore`, `tid` is not in core `c`'s run queue. -/
theorem removeRunnableOnCore_not_mem_self (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    tid ∉ (removeRunnableOnCore st tid c).scheduler.runQueueOnCore c := by
  rw [removeRunnableOnCore_runQueueOnCore_self]
  exact RunQueue.not_mem_remove_self _ tid

/-- WS-ZA ZA4.5: the removal takes `tid` off core `c`'s queue and moves no
other thread, nor `tid` on any other core, on or off a queue. -/
theorem removeRunnableOnCore_queuedOn (st : SystemState) (tid : SeLe4n.ThreadId) (c c' : CoreId)
    (y : SeLe4n.ThreadId) :
    (removeRunnableOnCore st tid c).queuedOn c' y =
      if y = tid ∧ c' = c then false else st.queuedOn c' y :=
  SystemState.runDescheduleOnCore_queuedOn st c tid c' y

/-- After `removeRunnableOnCore`, `tid` is not core `c`'s current thread. -/
theorem removeRunnableOnCore_currentOnCore_ne_self (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.currentOnCore c ≠ some tid := by
  rw [removeRunnableOnCore_currentOnCore_self]
  split
  · simp
  · assumption

/-- Cross-core frame: `removeRunnableOnCore` on core `c` leaves a *different*
core `c'`'s run-queue slot untouched (per-core locality). -/
theorem removeRunnableOnCore_runQueueOnCore_ne (st : SystemState)
    (tid : SeLe4n.ThreadId) (c c' : CoreId) (h : c ≠ c') :
    (removeRunnableOnCore st tid c).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
  simp [removeRunnableOnCore, SchedulerState.setCurrentOnCore_runQueueOnCore,
    SchedulerState.setRunQueueOnCore_runQueueOnCore_ne, h]

/-- Cross-core frame: `removeRunnableOnCore` on core `c` leaves a *different*
core `c'`'s current slot untouched (per-core locality). -/
theorem removeRunnableOnCore_currentOnCore_ne (st : SystemState)
    (tid : SeLe4n.ThreadId) (c c' : CoreId) (h : c ≠ c') :
    (removeRunnableOnCore st tid c).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  simp [removeRunnableOnCore, SchedulerState.setRunQueueOnCore_currentOnCore,
    SchedulerState.setCurrentOnCore_currentOnCore_ne, h]

/-- `enqueueRunnableOnCore` leaves every core's active-domain slot untouched. -/
theorem enqueueRunnableOnCore_activeDomainOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueRunnableOnCore st c tid).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' := by
  rcases enqueueRunnableOnCore_scheduler_cases st c tid with h | ⟨E, p, h⟩ <;> rw [h]
  simp only [SchedulerState.markReschedulePendingOnCore_activeDomainOnCore,
    SchedulerState.setRunQueueOnCore_activeDomainOnCore, SchedulerState.setRunQueueEndsOnCore_activeDomainOnCore]

/-- `enqueueRunnableOnCore` leaves every core's domain-time-remaining slot. -/
theorem enqueueRunnableOnCore_domainTimeRemainingOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueRunnableOnCore st c tid).scheduler.domainTimeRemainingOnCore c'
      = st.scheduler.domainTimeRemainingOnCore c' := by
  rcases enqueueRunnableOnCore_scheduler_cases st c tid with h | ⟨E, p, h⟩ <;> rw [h]
  simp only [SchedulerState.markReschedulePendingOnCore_domainTimeRemainingOnCore,
    SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore, SchedulerState.setRunQueueEndsOnCore_domainTimeRemainingOnCore]

/-- `enqueueRunnableOnCore` leaves every core's domain-schedule-index slot. -/
theorem enqueueRunnableOnCore_domainScheduleIndexOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueRunnableOnCore st c tid).scheduler.domainScheduleIndexOnCore c'
      = st.scheduler.domainScheduleIndexOnCore c' := by
  rcases enqueueRunnableOnCore_scheduler_cases st c tid with h | ⟨E, p, h⟩ <;> rw [h]
  simp only [SchedulerState.markReschedulePendingOnCore_domainScheduleIndexOnCore,
    SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore, SchedulerState.setRunQueueEndsOnCore_domainScheduleIndexOnCore]

/-- `enqueueRunnableOnCore` leaves the machine registers untouched. -/
theorem enqueueRunnableOnCore_machineEq (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : (enqueueRunnableOnCore st c tid).machine = st.machine := by
  have h := enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c tid
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

/-- `removeRunnableOnCore` leaves every core's machine registers untouched. -/
theorem removeRunnableOnCore_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) : (removeRunnableOnCore st tid c).machine = st.machine := by
  have h := removeRunnableOnCore_onlyObjectsSchedulerDiffer st tid c
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

/-- `removeRunnableOnCore` leaves every core's active-domain slot untouched. -/
theorem removeRunnableOnCore_activeDomainOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (c c' : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' := by
  simp [removeRunnableOnCore, SchedulerState.setCurrentOnCore_activeDomainOnCore,
    SchedulerState.setRunQueueOnCore_activeDomainOnCore]

/-- `removeRunnableOnCore` leaves every core's domain-time-remaining slot. -/
theorem removeRunnableOnCore_domainTimeRemainingOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c c' : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.domainTimeRemainingOnCore c'
      = st.scheduler.domainTimeRemainingOnCore c' := by
  simp [removeRunnableOnCore, SchedulerState.setCurrentOnCore_domainTimeRemainingOnCore,
    SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore]

/-- `removeRunnableOnCore` leaves every core's domain-schedule-index slot. -/
theorem removeRunnableOnCore_domainScheduleIndexOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c c' : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.domainScheduleIndexOnCore c'
      = st.scheduler.domainScheduleIndexOnCore c' := by
  simp [removeRunnableOnCore, SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore,
    SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]

/-- `v0.35.158`: `placedCoreOf?` reads one bit per core of each of its two
slices — *is `tid` in this queue*, *is `tid` this core's current thread* — so two
states agreeing on those two bits at every core place `tid` alike.  The finest of
the three congruences, and the one a removal of some OTHER thread satisfies: that
removal may clear a current slot, so the slot itself is not equal, but the bit
"is it `tid`" is. -/
theorem placedCoreOf?_congr_of_bits {st st' : SystemState} (tid : SeLe4n.ThreadId)
    (h : ∀ c : CoreId,
      st'.queuedOn c tid = st.queuedOn c tid
      ∧ (st'.scheduler.currentOnCore c == some tid)
        = (st.scheduler.currentOnCore c == some tid)) :
    placedCoreOf? st' tid = placedCoreOf? st tid := by
  unfold placedCoreOf?
  have hp : (fun c : CoreId => st'.queuedOn c tid
      || st'.scheduler.currentOnCore c == some tid)
      = (fun c : CoreId => st.queuedOn c tid
      || st.scheduler.currentOnCore c == some tid) := by
    funext c; rw [(h c).1, (h c).2]
  rw [hp]

/-- `v0.35.158`: the resolver's `none` is "on no scheduler slot at any core" —
the pointwise form of `placedCoreOf?_isSome_iff`, which is what a consumer
asserting *this thread consumes no CPU* reads. -/
theorem placedCoreOf?_none_iff (st : SystemState) (tid : SeLe4n.ThreadId) :
    placedCoreOf? st tid = none
      ↔ ∀ c : CoreId, st.queuedOn c tid = false
          ∧ st.scheduler.currentOnCore c ≠ some tid := by
  have hIs := placedCoreOf?_isSome_iff st tid
  constructor
  · intro hP c
    rw [hP, Option.isSome_none] at hIs
    obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp hIs.symm
    unfold runnableOnSomeCore at h1
    unfold runningOnSomeCore at h2
    rw [List.any_eq_false] at h1 h2
    have h1c := h1 c (SeLe4n.Kernel.Concurrency.mem_allCores c)
    have h2c := h2 c (SeLe4n.Kernel.Concurrency.mem_allCores c)
    simp only [Bool.not_eq_true] at h1c h2c
    exact ⟨h1c, fun hCur => by rw [hCur] at h2c; simp at h2c⟩
  · intro h
    cases hP : placedCoreOf? st tid with
    | none => rfl
    | some c =>
      have hs := placedCoreOf?_sound st tid c hP
      rcases Bool.or_eq_true_iff.mp hs with h1 | h2
      · rw [(h c).1] at h1; exact absurd h1 Bool.false_ne_true
      · exact absurd (by simpa using h2) (h c).2

/-- `v0.35.158`: under single placement — the thread is queued or current on at
most one core — the state-resolved removal takes it off **every** scheduler
slot: the resolved core by the removal, every other core vacuously.  Stated at
the primitive, beside its definition, because the reply path's donation return
and the cancellation reclaim both perform this removal on the thread they unbind
and both want the same conclusion of it. -/
theorem descheduleAtPlacement_unplaced (st : SystemState) (tid : SeLe4n.ThreadId)
    (hUnique : ∀ c c' : CoreId,
        (st.queuedOn c tid = true ∨ st.scheduler.currentOnCore c = some tid) →
        (st.queuedOn c' tid = true ∨ st.scheduler.currentOnCore c' = some tid) →
        c = c') :
    placedCoreOf? (descheduleAtPlacement st tid) tid = none := by
  rw [placedCoreOf?_none_iff]
  intro c
  cases hP : placedCoreOf? st tid with
  | none =>
    simp only [descheduleAtPlacement, descheduleAt, hP]
    exact (placedCoreOf?_none_iff st tid).mp hP c
  | some p =>
    simp only [descheduleAtPlacement, descheduleAt, hP]
    by_cases hc : c = p
    · subst hc
      exact ⟨by rw [removeRunnableOnCore_queuedOn, if_pos ⟨rfl, rfl⟩],
        removeRunnableOnCore_currentOnCore_ne_self st tid c⟩
    · rw [removeRunnableOnCore_queuedOn, if_neg (fun h => hc h.2),
        removeRunnableOnCore_currentOnCore_ne st tid p c (fun h => hc h.symm)]
      have hp := placedCoreOf?_sound st tid p hP
      have hPlacedP : st.queuedOn p tid = true
          ∨ st.scheduler.currentOnCore p = some tid := by
        rcases Bool.or_eq_true_iff.mp hp with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (by simpa using h2)
      refine ⟨?_, fun hCurC => hc (hUnique c p (Or.inr hCurC) hPlacedP)⟩
      cases hq : st.queuedOn c tid with
      | false => rfl
      | true => exact absurd (hUnique c p (Or.inl hq) hPlacedP) hc

/-- `v0.35.158`: the state-resolved removal of one thread places no OTHER thread
differently — the removal clears a current slot only where it held the removed
thread, and takes only the removed thread out of a queue.  The congruence the
cancellation composite reads for the victim after the reclaim has descheduled
the holder. -/
theorem descheduleAtPlacement_placedCoreOf?_ne (st : SystemState) (tid x : SeLe4n.ThreadId)
    (hne : x ≠ tid) :
    placedCoreOf? (descheduleAtPlacement st tid) x = placedCoreOf? st x := by
  apply placedCoreOf?_congr_of_bits x
  intro c
  unfold descheduleAtPlacement descheduleAt
  cases hP : placedCoreOf? st tid with
  | none => exact ⟨rfl, rfl⟩
  | some p =>
    by_cases hc : p = c
    · subst hc
      refine ⟨?_, ?_⟩
      · rw [removeRunnableOnCore_queuedOn, if_neg (fun h => hne h.1)]
      · rw [removeRunnableOnCore_currentOnCore_self]
        split
        · rename_i hCur
          rw [hCur]
          apply Bool.eq_iff_iff.mpr
          constructor
          · intro h; simp at h
          · intro h
            simp only [beq_iff_eq, Option.some.injEq] at h
            exact absurd h.symm hne
        · rfl
    · rw [removeRunnableOnCore_queuedOn, if_neg (fun h => hc h.2.symm),
        removeRunnableOnCore_currentOnCore_ne st tid p c hc]
      exact ⟨rfl, rfl⟩



/-- WS-SM SM5.C.2 (plan §3.3, Theorem 3.3.1): cross-core wake.

Determines `tid`'s target core (`determineTargetCore`), makes it runnable on
that core (`enqueueRunnableOnCore`), and decides whether a cross-core
`.reschedule` SGI is required: if the target core differs from the
`executingCore` (the core currently running the wake), the target must be poked
to re-run its scheduler, so the wake returns `some (target,
SgiKind.reschedule)`; if the target *is* the executing core, the local
scheduler will pick up the newly-runnable thread on its next decision, so no SGI
is needed (`none`).

Returns the post-wake state paired with the optional SGI to emit.  The pure
single-state-plus-SGI form (rather than the `BaseIO` form that actually fires
the SGI over the FFI) mirrors `chooseThreadOnCore` / `switchToThreadOnCore`:
SM5.C's runtime dispatch loop reads the executing core from `TPIDR_EL1`
(`Concurrency.currentCoreId`), commits the state under the `wakeThreadLockSet`
`withLockSet` bracket, then emits the returned SGI via `Concurrency.emitWakeSgi`
*after* the state write is visible (the BKL-discipline ordering — SM5.C.4 —
guaranteed on the Rust side by the `dsb ish` that `ffi_send_sgi` emits before
writing `GICD_SGIR`). -/
def wakeThread (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) : SystemState × Option (CoreId × SgiKind) :=
  let target := determineTargetCore st tid
  let st' := enqueueRunnableOnCore st target tid
  -- SGI decision (SM5.C.4, audit-pass-1: ghost-wake guard).  Emit a cross-core
  -- `.reschedule` SGI iff the wake *actually* made `tid` runnable on a *remote*
  -- core — i.e. iff `tid` resolves to a TCB (so `enqueueRunnableOnCore` was not a
  -- fail-closed no-op) AND the target is not the executing core.  Guarding on
  -- `getTcb?` keeps the SGI emission *consistent with the state effect*: a wake
  -- of a thread that does not resolve to a TCB enqueues nothing, so it must not
  -- poke a remote core (which would otherwise run its scheduler for no reason —
  -- wasted cross-core work on a corrupted-state path).  Well-formed callers wake
  -- real threads, so the happy path is unchanged.
  let sgi : Option (CoreId × SgiKind) :=
    match st.getTcb? tid with
    | none   => none
    | some _ => if target == executingCore then none else some (target, SgiKind.reschedule)
  (st', sgi)

/-- WS-ZA ZA4.7: the compiled `wakeThread`.  The SGI is decided from the
pre-state before the enqueue writes, so nothing keeps the pre-state across the
writes (`ZERO_ALLOCATION_SYSCALL_PLAN.md` D1).  Inlined, so a caller
projects the state and the SGI where it uses them and the pair is never built.
Proven equal (`wakeThread_eq_impl`). -/
@[inline] def wakeThreadImpl (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) : SystemState × Option (CoreId × SgiKind) :=
  let target := determineTargetCore st tid
  match st.getTcb? tid with
  | none => (enqueueRunnableOnCore st target tid, none)
  | some _ =>
      if target == executingCore then (enqueueRunnableOnCore st target tid, none)
      else (enqueueRunnableOnCore st target tid, some (target, SgiKind.reschedule))

@[csimp] theorem wakeThread_eq_impl : @wakeThread = @wakeThreadImpl := by
  funext st tid executingCore
  unfold wakeThread wakeThreadImpl
  cases st.getTcb? tid with
  | none => rfl
  | some _ => simp only []; split <;> rfl

/-- WS-SM SM5.C.5 (audit-pass-3; selection-aligned since PR #880 round 7): does
the budget-eligible candidate `tid` outrank core `c`'s current thread — in the
**selector's own strict-preference order**?

- `true` when the core is idle (`currentOnCore c = none`) — no running thread to
  protect, so the candidate dispatches.
- otherwise, `true` exactly when `isBetterCandidate` prefers the candidate over
  the current thread on their **resolved** effective scheduling parameters
  (`resolveEffectivePrioDeadline`): strictly higher effective priority, or — at
  equal effective priority — an earlier resolved deadline, where "no deadline"
  (`0`) loses to any deadline and equal deadlines keep FIFO, so no gratuitous
  preemption fires and a lower-priority or later-deadline candidate waits in
  the run queue for the next scheduling point.

**Why resolved parameters (PR #880 round 7).**  The selector this gate
predicts (`chooseThreadEffectiveOnCore` → `chooseBestRunnableEffective`)
orders candidates by `resolveEffectivePrioDeadline` — for a bound or donated
thread the SchedContext's *deadline*, with the PIP boost composed on top.  For
*priorities* a TCB-field comparison is sound, and since WS-RR (`v0.35.133`)
**unconditionally**: with `TCB.priority` the base's one home the resolver's
first component *is* `tcb.boostedPriority` at every binding, which
`resolveEffectivePrioDeadline_fst_eq_boostedPriority` (above) states with no
hypothesis.  Until that cut it read `sc.priority` at `.bound`, so the bridge
needed the `boundThreadPriorityConsistent` agreement the bind and configure
propagations establish — do not read this paragraph as still resting on them.
**Deadlines have no such one home**: bind copies only the priority, and
`schedContextConfigure` / `cbsUpdateDeadline` move the SC deadline with the
TCB field untouched.  A TCB-deadline comparison (the round-6 form) therefore
diverged from the selector exactly for the bound threads CBS scheduling
exists for: two equal-priority bound threads with TCB deadlines `0` and SC
deadlines 20 / 10 select the earlier-deadline candidate at any scheduling
point, while the TCB-based gate refused the very poke that creates that
scheduling point.  Comparing what selection compares closes the gap by
construction — `candidateOutranksCurrentOnCore_eq_isBetterCandidate` pins the
gate to the selector's ordering, so `handleRescheduleSgiOnCore` (which applies
this gate to the selector's own choice) is exactly "switch iff the selector's
best strictly beats the incumbent".

Two deliberate consequences of the alignment, both matching what selection
would do at the next scheduling point: an equal-effective-priority
**deadline-bearing candidate now displaces a deadline-less current** (the
selector's challenger-has-deadline arm — EDF treats "no deadline" as latest),
and the round-6 same-domain / equal-base-priority conjuncts are gone — the
live consumer's candidate is already domain-filtered by
`chooseThreadEffectiveOnCore`, and selection orders by effective (not base)
priority.  The `_, _ => true` arm (current TID does not resolve to a TCB) is
unreachable under `currentThreadValidOnCore`; it dispatches the
run-queue-validated candidate as a making-progress recovery rather than
keeping a corrupt current. -/
def candidateOutranksCurrentOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : Bool :=
  match st.scheduler.currentOnCore c with
  | none => true
  | some curTid =>
      match st.getTcb? curTid, st.getTcb? tid with
      | some curTcb, some tidTcb =>
          isBetterCandidate (resolveEffectivePrioDeadline st curTcb).1
            (resolveEffectivePrioDeadline st curTcb).2
            (resolveEffectivePrioDeadline st tidTcb).1
            (resolveEffectivePrioDeadline st tidTcb).2
      | _, _ => true

/-- WS-SM (PR #880 round 7, the alignment contract): with a resolving current
and candidate, the preemption gate **is** the selector's strict-preference
relation `isBetterCandidate`, applied to the same
`resolveEffectivePrioDeadline` parameters `chooseBestRunnableEffective` orders
by.  The gate and the selection it predicts cannot diverge — on any pair of
scheduling parameters, bound, donated or unbound. -/
theorem candidateOutranksCurrentOnCore_eq_isBetterCandidate (st : SystemState)
    (c : CoreId) (tid curTid : SeLe4n.ThreadId) (curTcb tidTcb : TCB)
    (hCur : st.scheduler.currentOnCore c = some curTid)
    (hCurTcb : st.getTcb? curTid = some curTcb)
    (hTidTcb : st.getTcb? tid = some tidTcb) :
    candidateOutranksCurrentOnCore st c tid =
      isBetterCandidate (resolveEffectivePrioDeadline st curTcb).1
        (resolveEffectivePrioDeadline st curTcb).2
        (resolveEffectivePrioDeadline st tidTcb).1
        (resolveEffectivePrioDeadline st tidTcb).2 := by
  unfold candidateOutranksCurrentOnCore
  simp only [hCur, hCurTcb, hTidTcb]

/-- WS-ZA ZA5.2: the deadline half of `resolveEffectivePrioDeadline`, as a
word: the bound or donated reservation's deadline, else the thread's own. -/
@[inline] def resolvedDeadlineCode (st : SystemState) (tcb : TCB) : Nat :=
  match tcb.schedContextBinding with
  | .unbound => tcb.deadline.val
  | .bound scId | .donated scId _ =>
    match st.getSchedContext? scId with
    | some sc => sc.deadline.val
    | none => tcb.deadline.val

theorem resolvedDeadlineCode_eq (st : SystemState) (tcb : TCB) :
    resolvedDeadlineCode st tcb = (resolveEffectivePrioDeadline st tcb).2.val := by
  unfold resolvedDeadlineCode resolveEffectivePrioDeadline
  cases tcb.schedContextBinding <;> simp only <;> split <;> rfl

theorem resolveEffectivePrioDeadline_fst_raisedBy (st : SystemState) (tcb : TCB) :
    (resolveEffectivePrioDeadline st tcb).1 = tcb.priority.raisedBy tcb.pipBoost := by
  unfold resolveEffectivePrioDeadline
  cases tcb.schedContextBinding <;> simp only <;> split <;> rfl

/-- WS-ZA ZA5.2: `isBetterCandidate` over the words its arguments wrap. -/
@[inline] def isBetterCandidateCode (incPrio incDeadline chalPrio chalDeadline : Nat) : Bool :=
  if chalPrio > incPrio then true
  else if chalPrio < incPrio then false
  else
    match chalDeadline, incDeadline with
    | 0, _ => false
    | _, 0 => true
    | cd, id => cd < id

/-- WS-ZA ZA5.2: the compiled `candidateOutranksCurrentOnCore`.  The core's
current thread is read as its code and each side's parameters as words, so
neither the `some` of the current slot nor a priority/deadline pair is built. -/
def candidateOutranksCurrentOnCoreImpl (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : Bool :=
  match st.scheduler.currentCode.get c with
  | 0 => true
  | k + 1 =>
    match st.getTcb? ⟨k⟩ with
    | none => true
    | some curTcb =>
      match st.getTcb? tid with
      | none => true
      | some tidTcb =>
        isBetterCandidateCode (curTcb.priority.raisedBy curTcb.pipBoost).val
          (resolvedDeadlineCode st curTcb)
          (tidTcb.priority.raisedBy tidTcb.pipBoost).val (resolvedDeadlineCode st tidTcb)

@[csimp] theorem candidateOutranksCurrentOnCore_eq_impl :
    @candidateOutranksCurrentOnCore = @candidateOutranksCurrentOnCoreImpl := by
  funext st c tid
  unfold candidateOutranksCurrentOnCore candidateOutranksCurrentOnCoreImpl
  simp only [SchedulerState.currentOnCore]
  cases st.scheduler.currentCode.get c with
  | zero => rfl
  | succ k =>
    simp only [SeLe4n.ThreadId.ofOptCode]
    cases st.getTcb? ⟨k⟩ with
    | none => rfl
    | some curTcb =>
      cases st.getTcb? tid with
      | none => rfl
      | some tidTcb =>
        simp only [resolvedDeadlineCode_eq, resolveEffectivePrioDeadline_fst_raisedBy,
          isBetterCandidateCode, isBetterCandidate]
        rfl

/-- WS-SM (PR #880 round 7): the preemption gate fires on EDF displacement over
the **resolved** deadlines — at equal resolved effective priority, a candidate
whose resolved deadline is set and earlier than the current thread's (where a
deadline-less current counts as latest) opens the gate, so the wake's
`.reschedule` results in a switch at the receiver instead of being dropped
until a later timer scheduling point.  This is the round-6 EDF-displacement
property restated on the parameters selection actually compares — a bound
thread's SchedContext deadline now displaces, even while both TCB deadline
fields sit at `0`. -/
theorem candidateOutranksCurrentOnCore_of_edf_earlier (st : SystemState)
    (c : CoreId) (tid curTid : SeLe4n.ThreadId) (curTcb tidTcb : TCB)
    (hCur : st.scheduler.currentOnCore c = some curTid)
    (hCurTcb : st.getTcb? curTid = some curTcb)
    (hTidTcb : st.getTcb? tid = some tidTcb)
    (hPrio : (resolveEffectivePrioDeadline st curTcb).1.toNat
        = (resolveEffectivePrioDeadline st tidTcb).1.toNat)
    (hTidDl : (resolveEffectivePrioDeadline st tidTcb).2.toNat ≠ 0)
    (hEarlier : (resolveEffectivePrioDeadline st curTcb).2.toNat = 0 ∨
        (resolveEffectivePrioDeadline st tidTcb).2.toNat
          < (resolveEffectivePrioDeadline st curTcb).2.toNat) :
    candidateOutranksCurrentOnCore st c tid = true := by
  rw [candidateOutranksCurrentOnCore_eq_isBetterCandidate st c tid curTid
    curTcb tidTcb hCur hCurTcb hTidTcb]
  unfold isBetterCandidate
  rw [if_neg (by omega), if_neg (by omega)]
  cases hTid : (resolveEffectivePrioDeadline st tidTcb).2.toNat with
  | zero => exact absurd hTid hTidDl
  | succ n =>
      cases hCurD : (resolveEffectivePrioDeadline st curTcb).2.toNat with
      | zero => rfl
      | succ m =>
          simp only [decide_eq_true_eq]
          omega

/-- Is core `c`'s current thread outside the core's active domain?  `false` for
an idle core, for the core's own idle thread (whose dispatch the idle fallback
gates on its domain, and which no scheduling context can bind, so no domain
write reaches it) and for a current thread that resolves to no TCB.  Under
`currentThreadInActiveDomainOnCore` it is always `false`; it turns `true` when
a write moves a running thread's `domain` — a scheduling-context reconfigure
(`schedContextConfigureBoundPropagate`) is the one such writer — and the
reschedule flag that write raises is what brings the core to
`handleRescheduleSgiOnCore`, which then drops the incumbent. -/
def currentOutsideActiveDomainOnCore (st : SystemState) (c : CoreId) : Bool :=
  match st.scheduler.currentOnCore c with
  | none => false
  | some tid =>
      if tid == idleThreadId c then false
      else
        match st.getTcb? tid with
        | some tcb => tcb.domain != st.scheduler.activeDomainOnCore c
        | none => false

/-- Take core `c`'s current thread off the core with nothing dispatched in its
place: save its context and put it back in core `c`'s run queue
(`preemptCurrentOnCore`, against the core's idle-thread id, which is never a
dispatched user thread), then clear the `current` slot — the legacy idle
representation a remote deschedule leaves.  The thread stays runnable. -/
def dropCurrentOnCore (st : SystemState) (c : CoreId) : SystemState :=
  let st1 := preemptCurrentOnCore st c (idleThreadId c)
  { st1 with scheduler := st1.scheduler.setCurrentOnCore c none }

/-- WS-SM SM5.C.5 (plan §4.4): the target core's `.reschedule` SGI handler.

When core `c` takes a `.reschedule` SGI (sent by a remote wake), it re-runs its
own scheduler: re-choose the highest-priority *budget-eligible* runnable thread
in its run queue (`chooseThreadEffectiveOnCore`, SM5.A §6 — the CBS/SchedContext
selector the production timer path uses, so a reschedule cannot dispatch a
budget-exhausted thread) and, **only if that candidate outranks the current
thread** (`candidateOutranksCurrentOnCore` — the selector's own
strict-preference order over the resolved effective parameters: strictly
higher effective priority, or an earlier resolved deadline at equal effective
priority, PR #880 round 7), switch to it (`switchToThreadOnCore`, SM5.B).
Since the gate *is* `isBetterCandidate` on `resolveEffectivePrioDeadline`
(`candidateOutranksCurrentOnCore_eq_isBetterCandidate`), this handler is
exactly "switch iff the selector's best strictly beats the incumbent".
Consumed by the `.reschedule` SGI receiver (`PerCoreRescheduleEntry`), by
`resumeThread` / the PIP deboost path for their **local** wake arms (PR #811
P2-5 — no SGI can poke the core that is already executing), and — PR #880
round 7 — by `timerTickOnCore` after a local CBS-replenishment wake, the
tick's own local counterpart of the same receiver decision.

- `chooseThreadEffectiveOnCore` never errors (`chooseThreadEffectiveOnCore_ne_error`),
  and a candidate `switchToThreadOnCore` refuses is treated as no candidate,
  so the handler never refuses (`handleRescheduleSgiOnCore_eq_state`).
- returns `none` (no budget-eligible thread) → no switch; core `c` keeps running
  (or idles).  Identity (`.ok st`); never invents a dispatch — unless the
  incumbent is outside the core's active domain
  (`currentOutsideActiveDomainOnCore`), which the selector would never have
  picked: then it is dropped (`dropCurrentOnCore`, re-queued, core left idle).
- returns `some tid` and the incumbent is outside the active domain → switch to
  `tid` whatever their priorities (the incumbent is no contender).
- returns `some tid` and `tid` outranks current (or core idle) → switch to `tid`
  (`switchToThreadOnCore` preempts the old current back into the run queue and
  dispatches `tid`).
- returns `some tid` but current still outranks `tid` → **keep current**
  (`.ok st`).  This is the audit-pass-3 / Codex-P1 fix: a *lower*-priority
  cross-core wake must NOT preempt a higher-priority running thread (fixed-
  priority preemptive policy).  Because the current thread is not in the run
  queue (dequeue-on-dispatch), the candidate is compared against it explicitly
  rather than competing inside `chooseThreadEffectiveOnCore`.

Two audit-pass-3 / Codex-P1 fixes land here: (1) **budget-awareness** — the
selector is `chooseThreadEffectiveOnCore`, not the budget-skipping
`chooseThreadOnCore`, matching the production CBS timer path; (2) **preemption
policy** — the explicit `candidateOutranksCurrentOnCore` gate.

Composes the SM5.A selection and SM5.B switch.  Its lock-set
(`handleRescheduleSgiOnCoreLockSet`) is the switch's (object-store + run-queue
write locks), which subsumes both the selection's reads and the
`candidateOutranksCurrentOnCore` priority-comparison reads on the same two
domains. -/
def handleRescheduleSgiOnCore (st : SystemState) (c : CoreId) :
    Except KernelError SystemState :=
  -- The reschedule-SGI accumulator (KSC-1): this is a scheduling point on `c`,
  -- so every `.ok` arm ends by clearing `c`'s flag — AFTER the switch's own
  -- slot writes, which is what makes the flag mean "a point is owed" and not
  -- "a point was entered".
  match chooseThreadEffectiveOnCore st c with
  | .error e => .error e
  | .ok none =>
      -- An incumbent outside the active domain is dropped even with nothing to
      -- run in its place: the core idles rather than keep it.
      if currentOutsideActiveDomainOnCore st c then
        .ok ((dropCurrentOnCore st c).clearReschedulePendingOnCore c)
      else .ok (st.clearReschedulePendingOnCore c)
  | .ok (some tid) =>
      -- Any in-domain candidate displaces an out-of-domain incumbent.
      if currentOutsideActiveDomainOnCore st c || candidateOutranksCurrentOnCore st c tid then
        match switchToThreadOnCore st c tid with
        | .ok st' => .ok (st'.clearReschedulePendingOnCore c)
        -- WS-ZA ZA5.2: a candidate the core cannot run (one whose affinity
        -- forbids `c`, which the kernel invariants keep off `c`'s queue) is
        -- not dispatched: the core decides as if nothing were eligible, as
        -- seL4's `schedule` never fails.  A scheduling point does not refuse,
        -- so the operations that end in one check everything before writing.
        | .error _ =>
          if currentOutsideActiveDomainOnCore st c then
            .ok ((dropCurrentOnCore st c).clearReschedulePendingOnCore c)
          else .ok (st.clearReschedulePendingOnCore c)
      else .ok (st.clearReschedulePendingOnCore c)

/-- WS-ZA ZA5.2: core `c`'s decision when nothing is dispatched: an incumbent
outside the active domain is dropped, and the flag is cleared. -/
@[inline] def rescheduleNoCandidateOnCore (st : SystemState) (c : CoreId) : SystemState :=
  if currentOutsideActiveDomainOnCore st c then
    (dropCurrentOnCore st c).clearReschedulePendingOnCore c
  else st.clearReschedulePendingOnCore c

/-- WS-ZA ZA5.2: `handleRescheduleSgiOnCore`'s state, which it always reaches
(`handleRescheduleSgiOnCore_eq_state`): the handler never refuses.  The
selection is read as a thread code (`chooseThreadEffectiveOnCore_eq_code`) and
the switch's two checks (`switchToThreadOnCore`'s lookups) precede its writes,
so nothing keeps the state for a refusal and the switch writes in place
(WS-ZA ZA4.7 wrote this form for the local successor rule). -/
def handleRescheduleOnCoreState (st : SystemState) (c : CoreId) : SystemState :=
  match chooseThreadEffectiveOnCoreCode st c with
  | 0 => rescheduleNoCandidateOnCore st c
  | k + 1 =>
    let tid : SeLe4n.ThreadId := ⟨k⟩
    if currentOutsideActiveDomainOnCore st c || candidateOutranksCurrentOnCore st c tid then
      match st.getTcb? tid with
      | some tidTcb =>
        if affinityAdmitsCore tidTcb c then
          let stPreempt := preemptCurrentOnCore st c tid
          let stDequeued := stPreempt.runRemoveOnCore c tid
          let stRestored := restoreIncomingContextOnCoreUnlessCurrent stDequeued c tid
          { stRestored with scheduler := (stRestored.scheduler.setCurrentOnCore c (some tid))
            |>.clearReschedulePendingOnCore c }
        else rescheduleNoCandidateOnCore st c
      | none => rescheduleNoCandidateOnCore st c
    else st.clearReschedulePendingOnCore c

theorem handleRescheduleSgiOnCore_eq_state (st : SystemState) (c : CoreId) :
    handleRescheduleSgiOnCore st c = .ok (handleRescheduleOnCoreState st c) := by
  unfold handleRescheduleSgiOnCore handleRescheduleOnCoreState rescheduleNoCandidateOnCore
  rw [chooseThreadEffectiveOnCore_eq_code]
  cases chooseThreadEffectiveOnCoreCode st c with
  | zero =>
    by_cases hO : currentOutsideActiveDomainOnCore st c = true <;> simp only [hO] <;> rfl
  | succ k =>
    by_cases hG : (currentOutsideActiveDomainOnCore st c ||
        candidateOutranksCurrentOnCore st c ⟨k⟩) = true
    · simp only [hG, ↓reduceIte]
      unfold switchToThreadOnCore
      cases st.getTcb? ⟨k⟩ with
      | none =>
        by_cases hO : currentOutsideActiveDomainOnCore st c = true <;> simp only [hO] <;> rfl
      | some tidTcb =>
        by_cases hA : affinityAdmitsCore tidTcb c = true
        · simp only [hA, ↓reduceIte]; rfl
        · simp only [hA, Bool.false_eq_true, ↓reduceIte]
          by_cases hO : currentOutsideActiveDomainOnCore st c = true <;> simp only [hO] <;> rfl
    · simp only [hG, Bool.false_eq_true, ↓reduceIte]

/-- WS-SM SM5.C.8 (plan §3.3, §4.1): set a thread's CPU affinity.

The affinity-control transition: bind `targetTid` to a specific core
(`affinity = some c`) or unbind it (`affinity = none`, homed on the boot core).
After this, `determineTargetCore` wakes the thread onto the bound core, and
`switchToThreadOnCore`'s reject-remote gate (`affinityAdmitsCore`) admits it
only on that core.

Looks the target TCB up via the typed `getTcb?` accessor; writes the new
`cpuAffinity` back; fail-closed with `.invalidArgument` when `targetTid` is not
a TCB (mirroring `setPriorityOp`'s missing-target discipline).  Only the target
TCB is written — the scheduler state (run queues, current threads) is untouched.

**Authority (security contract).**  This transition performs **no** in-op
authority check — any caller reaching it can rebind any thread's affinity.
Unlike `setPriorityOp`, whose authority (the caller's maximum controlled
priority) is an intrinsic TCB field and is therefore validated in-op, CPU-
affinity authority is a *capability* (scheduler control), so the gate belongs at
the syscall-dispatch layer, not in this primitive: the future `tcbSetAffinity`
syscall MUST resolve and verify a scheduler-control capability (via
`syscallLookupCap`) *before* invoking `setThreadCpuAffinity`, exactly as every
other capability-gated transition is reached only past its dispatch check.  At
SM5.C the primitive is deliberately unwired — there is no `SyscallId` variant
and no `API` entry, so no dispatch path reaches it yet — and wiring it without
that capability gate would be a privilege-escalation (unauthorized thread-
placement / denial-of-service) regression.  Tracked as the SM5.C.8 dispatch
obligation for the SM5.D+ syscall surface.

**Migration note (SM5.H.4).**  Re-binding a thread that is *currently enqueued*
on a different core does not itself move it between run queues; the
SchedContext / run-queue migration on an affinity change is SM5.H.4.  At SM5.C
the field write is the affinity-control primitive; the new binding takes effect
on the thread's next wake (`determineTargetCore`) and the next reject-remote
check (`affinityAdmitsCore`). -/
def setThreadCpuAffinity (st : SystemState) (targetTid : SeLe4n.ThreadId)
    (affinity : Option CoreId) : Except KernelError SystemState :=
  match st.getTcbWitnessed? targetTid with
  | some ⟨tcb, h⟩ =>
      .ok (st.rewriteObject targetTid.toObjId (.tcb { tcb with cpuAffinity := affinity })
        (SystemState.rewriteAdmissible_tcb h _))
  | none => .error .invalidArgument

/-- WS-SM SM8.B.2: after the affinity write the thread's home core **is** the
requested affinity (boot when unbound) — the bridge that lets a write set or a
scheduler footprint name the new core without mentioning the mid-state.

Declared in the **staged** `InformationFlow/NonInterferenceCrossCore.lean` until
`v0.35.167`, where production could not read it; moved beside the definition it
is about, so the live `.tcbSetAffinity` arm's footprint can state that the
replenish pair it declares is the migration's own. -/
theorem setThreadCpuAffinity_determineTargetCore_eq (st stSet : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId) (hInv : st.objects.invExt)
    (hSet : setThreadCpuAffinity st tid affinity = .ok stSet) :
    determineTargetCore stSet tid = affinity.getD Concurrency.bootCoreId := by
  unfold setThreadCpuAffinity at hSet
  split at hSet
  · next tcb hTcb _ =>
    rw [Except.ok.injEq] at hSet
    subst hSet
    unfold determineTargetCore SystemState.getTcb?
    simp only [RHTable_getElem?_eq_get?, SystemState.rewriteObject_objects]
    rw [RHTable_getElem?_insert st.objects tid.toObjId
      (.tcb { tcb with cpuAffinity := affinity }) hInv tid.toObjId]
    simp only [beq_self_eq_true, if_pos]
    cases affinity <;> rfl
  · exact absurd hSet (by simp)

/-- WS-SM SM8.B.2: the affinity write is one typed object rewrite, so it touches
no scheduler state at all. -/
@[simp] theorem setThreadCpuAffinity_scheduler_eq (st stSet : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (hSet : setThreadCpuAffinity st tid affinity = .ok stSet) :
    stSet.scheduler = st.scheduler := by
  unfold setThreadCpuAffinity at hSet
  split at hSet
  · rw [Except.ok.injEq] at hSet; subst hSet; rfl
  · exact absurd hSet (by simp)

