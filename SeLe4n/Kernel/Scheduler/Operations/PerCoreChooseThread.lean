-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.Scheduler.Invariant.PerCore
import SeLe4n.Kernel.Concurrency.Locks.RwLock
import SeLe4n.Kernel.Concurrency.Locks.Kind
-- WS-RR RR7.11: `maxLockSetSize`, so the `_size_le_maxLockSetSize` theorems
-- below can state the bound their names claim rather than the numeral it holds.
import SeLe4n.Kernel.Concurrency.Locks.LockSet
import SeLe4n.Kernel.Scheduler.SchedFootprint

/-!
# WS-SM SM5.A — Per-core `chooseThread` (lock-set, independence, completeness)

This module is the SM5.A deliverable of the WS-SM Phase 5 per-core
scheduler (WS-SM SM5 §3.1, §5).
The per-core selection function `chooseThreadOnCore` itself lives in the
production module `Scheduler.Operations.Selection` (SM5.A.1), because the
legacy single-core `chooseThread` is now defined to delegate to it
(SM5.A.5).  This module collects the *forward-looking* SM5.A theorems —
the lock-set declaration, the per-core-independence frame, the
idle-fallback completeness theorems, the selection-soundness
(membership) result, and the decidability witnesses — staged until SM5's
per-core scheduler wires `chooseThreadOnCore` into a runtime dispatch
loop.

## What this module proves

* **SM5.A.2** the cross-domain `LockKey` + the unified
  `chooseThreadOnCoreLockSet` — the per-core run-queue lock key
  `LockKey.runQueue` (ordered by `CoreId`, at the §4.4 `LockKind.runQueue.level`)
  inside the one cross-domain lock key `LockKey` (the table lock, the
  object-domain `LockId`s, the run-queue and replenish-queue keys, with the
  plan §4.4 total order: every object lock precedes every run-queue lock —
  `LockKey.object_lt_runQueue`).  The read-only
  footprint of `chooseThreadOnCore c` is now the *complete* two-domain set
  `[(object objStore-table-lock, read), (runQueue c, read)]`: the object-store
  read lock guards the `st.objects.get?` TCB resolutions the selection performs,
  closing the run-queue-only footprint's under-locking gap.
* **SM5.A.3** per-core independence (Theorem 3.1.2): `chooseThreadOnCore_frame`
  + the named `chooseThreadOnCore_perCore_independence` + corollaries — the
  selection on core `c` reads only core `c`'s run-queue and active-domain
  slots; and selection **optimality** (Theorem 3.1.1):
  `chooseThreadOnCore_selects_highest` — no active-domain thread in the
  maximum-priority bucket beats the selection.
* **SM5.A.4** idle-fallback completeness — `chooseThreadOnCore` never errors on
  a well-formed state, returns `none` only when no in-domain runnable thread
  exists, and returns `some` whenever one is present (the foundation SM5.E
  discharges with the per-core idle thread).
* **SM5.A.6** `chooseThreadOnCore_some_mem_runQueueOnCore` (+ the literal
  `chooseThreadOnCore_preserves_wellFormed` anchor) — selection soundness.
* **SM5.A.7** decidability witnesses for the selection result.
* **Budget-aware companion (§6)** — the CBS-budget-aware `chooseThreadEffectiveOnCore`
  (its production def + legacy migration live in `Selection.lean`): per-core
  independence, non-erroring, completeness, selection soundness, and — unique to
  the budget variant — `chooseThreadEffectiveOnCore_selected_has_budget` (a
  dispatched thread genuinely has budget).

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId allCores
  LockKey)

-- ============================================================================
-- §1  SM5.A.2 — Per-core run-queue lock identifier + chooseThread lock-set
-- ============================================================================

-- The same-kind scheduler-lock segment, `schedFootprintOfCores` and the
-- SM5.H.4 parametric migration footprints are in
-- `Scheduler/SchedFootprint.lean` since WS-LS LS2.5, below every transition
-- module, so that a resolved footprint can sit beside its transition.

/-- WS-SM SM5.A.2 (cross-domain unification): the **complete** lock-set
footprint of `chooseThreadOnCore c`.

`chooseThreadOnCore c` reads two distinct kinds of state:
* core `c`'s run-queue slot and active-domain slot (the per-core scheduler
  state), and
* the RobinHood **object store** — it resolves every runnable thread's
  priority / deadline / domain through `st.objects.get?` (threaded into
  `chooseBestInBucket`).

The footprint therefore declares a lock from *both* domains, in plan §4.4
ascending order (object-domain lock first):
`[(LockKey.objStore, .read), (LockKey.runQueue c, .read)]`.

The object-store read lock (`LockKey.objStore`, the SM3.A.10 table-level
lock) is what makes the footprint sound under the SM5.B `withLockSet`
integration: holding it read-locked prevents a concurrent retype / delete /
write of a queued TCB from changing the selection (or turning it into
`schedulerInvariantViolation`) while only the run-queue lock is held.  The two
reads `chooseThreadOnCore_frame` identifies — `objects` and (`runQueueOnCore
c`, `activeDomainOnCore c`) — are guarded respectively by the object-store and
run-queue locks.  The cross-domain acquisition *order* is
`chooseThreadOnCoreLockSet_object_before_runQueue`; the *runtime* acquisition
wiring (`withLockSet`) is SM5.B. -/
def chooseThreadOnCoreLockSet (c : CoreId) :
    List (LockKey × Concurrency.AccessMode) :=
  [ (LockKey.objStore, .read)
  , (LockKey.runQueue c, .read) ]

/-- SM5.A.2 (cross-domain): the footprint is the two-lock object-store +
run-queue set. -/
@[simp] theorem chooseThreadOnCoreLockSet_length (c : CoreId) :
    (chooseThreadOnCoreLockSet c).length = 2 := rfl

/-- SM5.A.2: every lock in the `chooseThreadOnCore` footprint is acquired in
**read** mode — the selection is a pure read of both domains. -/
theorem chooseThreadOnCoreLockSet_read_only (c : CoreId) :
    ∀ p ∈ chooseThreadOnCoreLockSet c, p.2 = Concurrency.AccessMode.read := by
  intro p hp
  simp only [chooseThreadOnCoreLockSet, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with h | h <;> subst h <;> rfl

/-- SM5.A.2 (cross-domain — the audit-fix witness): the object-store read lock
is in the footprint, so the `st.objects.get?` TCB resolutions
`chooseThreadOnCore` performs are guarded.  This is the lock the run-queue-only
footprint omitted. -/
theorem chooseThreadOnCoreLockSet_contains_objStore_read (c : CoreId) :
    (LockKey.objStore, Concurrency.AccessMode.read)
      ∈ chooseThreadOnCoreLockSet c := by
  simp [chooseThreadOnCoreLockSet]

/-- SM5.A.2: the per-core run-queue read lock is in the footprint. -/
theorem chooseThreadOnCoreLockSet_contains_runQueue_read (c : CoreId) :
    (LockKey.runQueue c, Concurrency.AccessMode.read)
      ∈ chooseThreadOnCoreLockSet c := by
  simp [chooseThreadOnCoreLockSet]

/-- SM5.A.2 (plan §4.4): inside the footprint the object-store lock is
acquired *before* the run-queue lock — the cross-domain ascending order. -/
theorem chooseThreadOnCoreLockSet_object_before_runQueue (c : CoreId) :
    LockKey.objStore
      < LockKey.runQueue c :=
  LockKey.objStore_lt_runQueue _

/-- SM5.A.2: the footprint's projected keys are duplicate-free — the
object-store lock and the run-queue lock are distinct (different
constructors), mirroring the SM3.B `LockSet.hUniqueKeys` invariant. -/
theorem chooseThreadOnCoreLockSet_keys_nodup (c : CoreId) :
    ((chooseThreadOnCoreLockSet c).map (·.1)).Nodup := by
  simp [chooseThreadOnCoreLockSet]

/-- WS-SM SM5.A.2 / §6 (cross-domain unification): the lock-set footprint of the
budget-aware `chooseThreadEffectiveOnCore c`.

The budget-aware selector reads the same per-core scheduler state as
`chooseThreadOnCore` **plus** each candidate's SchedContext (via
`hasSufficientBudget` → `st.getSchedContext?`) — but both the TCB resolutions
and the SchedContext reads go through the *single* object store, so the
table-level object-store read lock (`LockKey.objStore`) already guards them.
The footprint therefore coincides with `chooseThreadOnCoreLockSet`:
`[(LockKey.objStore, .read), (LockKey.runQueue c, .read)]`.
The selector is production-reached (legacy `chooseThreadEffective` delegates to
it), so it carries the same complete two-domain footprint contract as its
non-budget sibling — closing the same under-locking gap on the budget path. -/
def chooseThreadEffectiveOnCoreLockSet (c : CoreId) :
    List (LockKey × Concurrency.AccessMode) :=
  chooseThreadOnCoreLockSet c

/-- SM5.A §6: the budget selector's footprint is exactly the non-budget
selector's (both read the object store + the per-core run queue). -/
@[simp] theorem chooseThreadEffectiveOnCoreLockSet_eq (c : CoreId) :
    chooseThreadEffectiveOnCoreLockSet c = chooseThreadOnCoreLockSet c := rfl

/-- SM5.A §6: the budget selector's footprint declares the object-store read
lock (guards both the TCB resolutions and the `hasSufficientBudget`
SchedContext reads). -/
theorem chooseThreadEffectiveOnCoreLockSet_contains_objStore_read (c : CoreId) :
    (LockKey.objStore, Concurrency.AccessMode.read)
      ∈ chooseThreadEffectiveOnCoreLockSet c :=
  chooseThreadOnCoreLockSet_contains_objStore_read c

/-- SM5.A §6: the budget selector's footprint declares the per-core run-queue
read lock. -/
theorem chooseThreadEffectiveOnCoreLockSet_contains_runQueue_read (c : CoreId) :
    (LockKey.runQueue c, Concurrency.AccessMode.read)
      ∈ chooseThreadEffectiveOnCoreLockSet c :=
  chooseThreadOnCoreLockSet_contains_runQueue_read c

/-- SM5.A §6: the budget selector's footprint is read-only (a pure read of both
domains). -/
theorem chooseThreadEffectiveOnCoreLockSet_read_only (c : CoreId) :
    ∀ p ∈ chooseThreadEffectiveOnCoreLockSet c,
      p.2 = Concurrency.AccessMode.read :=
  chooseThreadOnCoreLockSet_read_only c

-- ============================================================================
-- §2  SM5.A.3 — Per-core independence (plan §3.1, Theorem 3.1.2)
-- ============================================================================

/-- WS-SM SM5.A.3 (Theorem 3.1.2, frame form): `chooseThreadOnCore`'s read
footprint on core `c` is exactly `(objects, runQueueOnCore c,
activeDomainOnCore c)`.  Two states that agree on those three reads agree
on the selection.  Everything else about the two states — every *other*
core's run queue / active domain / current thread, the rest of the object
store's shape beyond the lookup function, the machine registers — is
irrelevant to the selection on core `c`.  This is the structural heart of
per-core independence. -/
theorem chooseThreadOnCore_frame (s₁ s₂ : SystemState) (c : CoreId)
    (hObj : s₁.objects = s₂.objects)
    (hRQ : s₁.scheduler.runQueueOnCore c = s₂.scheduler.runQueueOnCore c)
    (hAD : s₁.scheduler.activeDomainOnCore c = s₂.scheduler.activeDomainOnCore c) :
    chooseThreadOnCore s₁ c = chooseThreadOnCore s₂ c := by
  unfold chooseThreadOnCore
  have hGet : s₁.getObject? = s₂.getObject? := by
    unfold SeLe4n.Model.SystemState.getObject?; rw [hObj]
  rw [hGet, hRQ, hAD]

/-- WS-SM SM5.A.3 (Theorem 3.1.2): per-core independence under a run-queue
write.  Writing core `c'`'s run-queue slot (for `c' ≠ c`) leaves
`chooseThreadOnCore · c` unchanged — the selection on `c` cannot observe a
sibling core's run queue.  This is the property the SM5.A.2 read-only
lock-set encodes: cores outside the lock-set are not in the read
footprint. -/
theorem chooseThreadOnCore_independent_of_setRunQueueOnCore
    (s : SystemState) (c c' : CoreId) (rq : RunQueue) (h : c ≠ c') :
    chooseThreadOnCore
        { s with scheduler := s.scheduler.setRunQueueOnCore c' rq } c
      = chooseThreadOnCore s c := by
  apply chooseThreadOnCore_frame
  · rfl
  · exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne s.scheduler c' c rq (Ne.symm h)
  · exact SchedulerState.setRunQueueOnCore_activeDomainOnCore s.scheduler c' c rq

/-- WS-SM SM5.A.3: per-core independence under an active-domain write.
Writing core `c'`'s active-domain slot (for `c' ≠ c`) leaves
`chooseThreadOnCore · c` unchanged. -/
theorem chooseThreadOnCore_independent_of_setActiveDomainOnCore
    (s : SystemState) (c c' : CoreId) (d : SeLe4n.DomainId) (h : c ≠ c') :
    chooseThreadOnCore
        { s with scheduler := s.scheduler.setActiveDomainOnCore c' d } c
      = chooseThreadOnCore s c := by
  apply chooseThreadOnCore_frame
  · rfl
  · exact SchedulerState.setActiveDomainOnCore_runQueueOnCore s.scheduler c' c d
  · exact SchedulerState.setActiveDomainOnCore_activeDomainOnCore_ne s.scheduler c' c d (Ne.symm h)

/-- WS-SM SM5.A.3: `chooseThreadOnCore` does **not** read the `current`
slot at all — so a write to *any* core's current thread (including core
`c`'s own) leaves the selection unchanged.  Selection reads the run queue
and active domain; the current thread is set as a *consequence* of
selection (`switchToThreadOnCore`, SM5.B), never an input to it. -/
theorem chooseThreadOnCore_independent_of_setCurrentOnCore
    (s : SystemState) (c c' : CoreId) (v : Option SeLe4n.ThreadId) :
    chooseThreadOnCore
        { s with scheduler := s.scheduler.setCurrentOnCore c' v } c
      = chooseThreadOnCore s c := by
  apply chooseThreadOnCore_frame
  · rfl
  · exact SchedulerState.setCurrentOnCore_runQueueOnCore s.scheduler c' c v
  · exact SchedulerState.setCurrentOnCore_activeDomainOnCore s.scheduler c' c v

/-- WS-SM SM5.A.3 / SM5.A.2 bridge: a run-queue write on a core whose
run-queue lock is *not* a key of `chooseThreadOnCoreLockSet c` (equivalently,
any `c' ≠ c`) leaves the selection unchanged.  This connects the SM5.A.2
unified footprint to the SM5.A.3 independence result: the only run-queue lock
the footprint declares is `c`'s own, and that is precisely the run queue the
selection depends on.  (The footprint's *other* key — the object-store read
lock — guards the orthogonal `st.objects` read footprint, so it does not
appear in this run-queue-write statement.) -/
theorem chooseThreadOnCore_independent_of_write_off_lockSet
    (s : SystemState) (c c' : CoreId) (rq : RunQueue)
    (h : LockKey.runQueue c'
          ∉ (chooseThreadOnCoreLockSet c).map (·.1)) :
    chooseThreadOnCore
        { s with scheduler := s.scheduler.setRunQueueOnCore c' rq } c
      = chooseThreadOnCore s c := by
  have hne : c ≠ c' := by
    intro heq
    subst heq
    apply h
    simp [chooseThreadOnCoreLockSet]
  exact chooseThreadOnCore_independent_of_setRunQueueOnCore s c c' rq hne

/-- WS-SM SM5.A.3 (plan §3.1.2, the named `chooseThreadOnCore_perCore_independence`
form): the selection on core `c₁` does **not** depend on a distinct core
`c₂`'s run queue.  This is the plan's canonical statement of per-core
independence; it is exactly the run-queue-write corollary above, restated with
the plan's `c₁ ≠ c₂` variable naming for traceability. -/
theorem chooseThreadOnCore_perCore_independence
    (s : SystemState) (c₁ c₂ : CoreId) (h : c₁ ≠ c₂) (rq : RunQueue) :
    chooseThreadOnCore { s with scheduler := s.scheduler.setRunQueueOnCore c₂ rq } c₁
      = chooseThreadOnCore s c₁ :=
  chooseThreadOnCore_independent_of_setRunQueueOnCore s c₁ c₂ rq h

-- ============================================================================
-- §3  SM5.A.4 — Idle-fallback completeness (plan §3.5, Theorem 3.5.2)
-- ============================================================================
--
-- The completeness results rest on three structural facts about the
-- bucket-scan fold `chooseBestRunnableBy`, proved by induction on the
-- scanned list:
--
--   * once a candidate is recorded (`best = some _`) the scan never
--     "forgets" it (`_some_ne_ok_none`);
--   * a scan that finds nothing (`= .ok none`) means every scanned TCB was
--     ineligible (`_none_no_eligible`);
--   * a scan over a list of genuine TCBs never errors (`_ok_of_allTcb`).
--
-- These lift through `chooseBestInBucket` (max-bucket scan then full-list
-- fallback) to `chooseThreadOnCore`.

/-- SM5.A.4 helper: once the fold has recorded a candidate (`best = some
x`), it can never return `.ok none` — the recorded candidate is only ever
replaced by another `some`, never dropped.  (It may still `.error` if a
later list entry fails to resolve to a TCB.) -/
private theorem chooseBestRunnableBy_some_ne_ok_none
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (x : SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline),
      chooseBestRunnableBy objects eligible list (some x) ≠ .ok none := by
  intro list
  induction list with
  | nil => intro x h; simp [chooseBestRunnableBy] at h
  | cons hd tl ih =>
    intro x h
    obtain ⟨xt, xp, xd⟩ := x
    unfold chooseBestRunnableBy at h
    cases hObj : objects hd.toObjId with
    -- Round 15: a non-TCB entry is skipped, so the incumbent `some x` is carried
    -- into the tail unchanged and the inductive hypothesis still applies.
    | none => rw [hObj] at h; exact ih _ h
    | some obj =>
      cases obj with
      | tcb tcb =>
        rw [hObj] at h
        by_cases hElig : eligible tcb
        · by_cases hBetter : isBetterCandidate xp xd tcb.priority tcb.deadline
          · simp only [hElig, hBetter, if_true] at h; exact ih _ h
          · simp only [hElig, hBetter, if_true] at h; exact ih _ h
        · simp only [hElig] at h; exact ih _ h
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ | reply _ | frame _ | pageTable _ => rw [hObj] at h; exact ih _ h

/-- SM5.A.4 helper: a fold starting from `none` that returns `.ok none`
witnesses that **every** scanned TCB was ineligible.  (A non-TCB entry
would have produced `.error`, and an eligible TCB would have produced
`.ok (some _)` by `_some_ne_ok_none`.) -/
theorem chooseBestRunnableBy_none_no_eligible
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId),
      chooseBestRunnableBy objects eligible list none = .ok none →
      ∀ tid ∈ list, ∀ tcb : TCB,
        objects tid.toObjId = some (.tcb tcb) → eligible tcb = false := by
  intro list
  induction list with
  | nil => intro _ tid hmem; simp at hmem
  | cons hd tl ih =>
    intro h tid hmem tcb hObjTid
    have hHdReduce := h
    unfold chooseBestRunnableBy at hHdReduce
    rcases List.mem_cons.mp hmem with hEq | hMemTl
    · -- tid = hd: the recorded best would be `some` if eligible, so eligible = false
      subst hEq
      rw [hObjTid] at hHdReduce
      by_cases hElig : eligible tcb
      · exfalso
        simp only [hElig, if_true] at hHdReduce
        exact chooseBestRunnableBy_some_ne_ok_none objects eligible tl _ hHdReduce
      · exact eq_false_of_ne_true (by simpa using hElig)
    · -- tid ∈ tl: peel hd off and apply the induction hypothesis
      cases hHdObj : objects hd.toObjId with
      -- Round 15: a non-TCB head is skipped, so the tail fold is the same fold
      -- from `none` and the induction hypothesis applies directly.
      | none =>
        rw [hHdObj] at hHdReduce
        exact ih hHdReduce tid hMemTl tcb hObjTid
      | some obj =>
        cases obj with
        | tcb hdTcb =>
          rw [hHdObj] at hHdReduce
          by_cases hHdElig : eligible hdTcb
          · exfalso
            simp only [hHdElig, if_true] at hHdReduce
            exact chooseBestRunnableBy_some_ne_ok_none objects eligible tl _ hHdReduce
          · simp only [hHdElig] at hHdReduce
            exact ih hHdReduce tid hMemTl tcb hObjTid
        | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
        | schedContext _ | reply _ | frame _ | pageTable _ =>
          rw [hHdObj] at hHdReduce
          exact ih hHdReduce tid hMemTl tcb hObjTid

/-- SM5.A.4 helper: a fold over a list whose every entry resolves to a TCB
never errors — it returns `.ok _`.  This is the "no `schedulerInvariant`
violation under a well-formed run queue" property the idle-fallback
completeness rests on. -/
theorem chooseBestRunnableBy_ok_of_allTcb
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)),
      (∀ t ∈ list, ∃ tcb : TCB, objects t.toObjId = some (.tcb tcb)) →
      ∃ r, chooseBestRunnableBy objects eligible list best = .ok r := by
  intro list
  induction list with
  | nil => intro best _; exact ⟨best, rfl⟩
  | cons hd tl ih =>
    intro best hAll
    obtain ⟨hdTcb, hHdObj⟩ := hAll hd (List.mem_cons_self ..)
    have hAllTl : ∀ t ∈ tl, ∃ tcb : TCB, objects t.toObjId = some (.tcb tcb) :=
      fun t ht => hAll t (List.mem_cons_of_mem _ ht)
    unfold chooseBestRunnableBy
    rw [hHdObj]
    exact ih _ hAllTl

/-- WS-SM SM8.B (PR #861 review round 15): **the scan never errors, for any
list at all.**

This is what the skip arm buys, stated rather than left implicit.  Before it,
selection was total only under `runnableThreadsAreTCBs`
(`chooseBestRunnableBy_ok_of_allTcb`, directly above) — and when that invariant
was broken the failure was not local: the scan returned `.error`, so the core
could select *nothing*, for ever, since nothing on the error path removes the
offending entry.  The invariant is unchanged and still carried; what changed is
that the scheduler's liveness no longer rests on it.

`chooseBestRunnableBy_ok_of_allTcb` is kept because its callers pass the
hypothesis anyway, but it is now a corollary of this. -/
theorem chooseBestRunnableBy_always_ok
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)),
      ∃ r, chooseBestRunnableBy objects eligible list best = .ok r := by
  intro list
  induction list with
  | nil => intro best; exact ⟨best, rfl⟩
  | cons hd tl ih =>
    intro best
    unfold chooseBestRunnableBy
    cases objects hd.toObjId with
    | none => exact ih _
    | some obj => cases obj <;> exact ih _

/-- WS-SM SM8.B: the same, for the budget-aware scan the live SGI handler
reaches (`chooseThreadEffectiveOnCore` → `handleRescheduleSgiOnCore`). -/
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

/-- SM5.A.4 helper: the result of a fold (from any `best`) over a list of
genuine TCBs whose recorded candidate is `some (rt, _, _)` has `rt ∈ list`
or `rt` was already the recorded `best`.  Specialised to `best = none`
below to give selection soundness. -/
private theorem chooseBestRunnableBy_result_mem_aux
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
      (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline),
      chooseBestRunnableBy objects eligible list best = .ok (some (rt, rp, rd)) →
      rt ∈ list ∨ (∃ p d, best = some (rt, p, d)) := by
  intro list
  induction list with
  | nil =>
    intro best rt rp rd h
    simp only [chooseBestRunnableBy] at h
    exact Or.inr ⟨rp, rd, by rw [Except.ok.injEq] at h; rw [h]⟩
  | cons hd tl ih =>
    intro best rt rp rd h
    unfold chooseBestRunnableBy at h
    cases hObj : objects hd.toObjId with
    -- Round 15: a non-TCB head is skipped, so the fold continues on `tl` with
    -- `best` untouched and the two outcomes carry over unchanged.
    | none =>
      rw [hObj] at h
      rcases ih _ rt rp rd h with hTl | hb
      · exact Or.inl (List.mem_cons_of_mem _ hTl)
      · exact Or.inr hb
    | some obj =>
      cases obj with
      | tcb tcb =>
        rw [hObj] at h
        -- the fold continues on `tl` with an updated `best'`; analyse cases
        by_cases hElig : eligible tcb
        · cases best with
          | none =>
            simp only [hElig, if_true] at h
            rcases ih _ rt rp rd h with hTl | ⟨p, d, hb⟩
            · exact Or.inl (List.mem_cons_of_mem _ hTl)
            · simp only [Option.some.injEq, Prod.mk.injEq] at hb
              exact Or.inl (List.mem_cons.mpr (Or.inl hb.1.symm))
          | some y =>
            obtain ⟨yt, yp, yd⟩ := y
            by_cases hBetter : isBetterCandidate yp yd tcb.priority tcb.deadline
            · simp only [hElig, hBetter, if_true] at h
              rcases ih _ rt rp rd h with hTl | ⟨p, d, hb⟩
              · exact Or.inl (List.mem_cons_of_mem _ hTl)
              · simp only [Option.some.injEq, Prod.mk.injEq] at hb
                exact Or.inl (List.mem_cons.mpr (Or.inl hb.1.symm))
            · simp only [hElig, hBetter, if_true] at h
              rcases ih _ rt rp rd h with hTl | ⟨p, d, hb⟩
              · exact Or.inl (List.mem_cons_of_mem _ hTl)
              · exact Or.inr ⟨p, d, hb⟩
        · simp only [hElig] at h
          rcases ih _ rt rp rd h with hTl | hb
          · exact Or.inl (List.mem_cons_of_mem _ hTl)
          · exact Or.inr hb
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ | reply _ | frame _ | pageTable _ =>
        rw [hObj] at h
        rcases ih _ rt rp rd h with hTl | hb
        · exact Or.inl (List.mem_cons_of_mem _ hTl)
        · exact Or.inr hb

/-- SM5.A.4 / SM5.A.6 helper: selection soundness for a `none`-seeded
fold — a recorded candidate is a member of the scanned list. -/
theorem chooseBestRunnableBy_result_mem
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool)
    (list : List SeLe4n.ThreadId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (h : chooseBestRunnableBy objects eligible list none = .ok (some (rt, rp, rd))) :
    rt ∈ list := by
  rcases chooseBestRunnableBy_result_mem_aux objects eligible list none rt rp rd h with
    hMem | ⟨_, _, hb⟩
  · exact hMem
  · exact absurd hb (by simp)

-- ── Bridges through `chooseBestInBucket` (max-bucket scan + full-list
--    fallback) and the `chooseThreadOnCore` wrapper. ──

/-- SM5.A.4 helper: a `.ok none` from the bucket-first selector forces the
full-list fallback scan to also be `.ok none` (the max-bucket scan must
have been `.ok none` to reach the fallback). -/
theorem chooseBestInBucket_none_imp_toList_none
    (objects : SeLe4n.ObjId → Option KernelObject) (rq : RunQueue)
    (ad : SeLe4n.DomainId)
    (h : chooseBestInBucket objects rq ad = .ok none) :
    chooseBestRunnableInDomain objects rq.toList ad none = .ok none := by
  rw [bucketFirst_fullScan_equivalence] at h
  cases hMax : chooseBestRunnableInDomain objects rq.maxPriorityBucket ad none with
  | error e => rw [hMax] at h; simp at h
  | ok val =>
    cases val with
    | some r => rw [hMax] at h; simp at h
    | none => rw [hMax] at h; simpa using h

/-- SM5.A.4 helper: a bucket-first scan over a well-formed run queue whose
every member resolves to a TCB never errors.  The max-priority bucket is a
subset of the run queue (by well-formedness), so its members are also TCBs;
both the bucket scan and the full-list fallback therefore succeed. -/
theorem chooseBestInBucket_ok_of_allTcb
    (objects : SeLe4n.ObjId → Option KernelObject) (rq : RunQueue)
    (ad : SeLe4n.DomainId)
    (hwf : rq.wellFormed)
    (hAll : ∀ t ∈ rq.toList, ∃ tcb : TCB, objects t.toObjId = some (.tcb tcb)) :
    ∃ val, chooseBestInBucket objects rq ad = .ok val := by
  have hMaxAll : ∀ t ∈ rq.maxPriorityBucket, ∃ tcb : TCB,
      objects t.toObjId = some (.tcb tcb) := by
    intro t ht
    exact hAll t (RunQueue.membership_implies_flat rq t
      (RunQueue.maxPriorityBucket_subset rq hwf t ht))
  obtain ⟨maxVal, hMax⟩ :
      ∃ r, chooseBestRunnableInDomain objects rq.maxPriorityBucket ad none = .ok r :=
    chooseBestRunnableBy_ok_of_allTcb objects (fun tcb => tcb.domain == ad)
      rq.maxPriorityBucket none hMaxAll
  rw [bucketFirst_fullScan_equivalence, hMax]
  cases maxVal with
  | some r => exact ⟨some r, rfl⟩
  | none =>
    exact chooseBestRunnableBy_ok_of_allTcb objects (fun tcb => tcb.domain == ad)
      rq.toList none hAll

/-- SM5.A.6 helper: a selected candidate from the bucket-first scan over a
well-formed all-TCB run queue is a genuine member of the run queue's flat
list. -/
theorem chooseBestInBucket_result_mem
    (objects : SeLe4n.ObjId → Option KernelObject) (rq : RunQueue)
    (ad : SeLe4n.DomainId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (hwf : rq.wellFormed)
    (h : chooseBestInBucket objects rq ad = .ok (some (rt, rp, rd))) :
    rt ∈ rq.toList := by
  rw [bucketFirst_fullScan_equivalence] at h
  cases hMax : chooseBestRunnableInDomain objects rq.maxPriorityBucket ad none with
  | error e => rw [hMax] at h; simp at h
  | ok val =>
    cases val with
    | some r =>
      rw [hMax] at h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      have hrtMem : rt ∈ rq.maxPriorityBucket :=
        chooseBestRunnableBy_result_mem objects (fun tcb => tcb.domain == ad)
          rq.maxPriorityBucket rt rp rd hMax
      exact RunQueue.membership_implies_flat rq rt
        (RunQueue.maxPriorityBucket_subset rq hwf rt hrtMem)
    | none =>
      rw [hMax] at h
      exact chooseBestRunnableBy_result_mem objects (fun tcb => tcb.domain == ad)
        rq.toList rt rp rd h

/-- SM5.A.4 helper: `chooseThreadOnCore = .ok none` forces the underlying
bucket-first scan to be `.ok none`. -/
theorem chooseThreadOnCore_eq_none_imp_bucket_none
    (st : SystemState) (c : CoreId) (h : chooseThreadOnCore st c = .ok none) :
    chooseBestInBucket st.getObject? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok none := by
  unfold chooseThreadOnCore at h
  cases hB : chooseBestInBucket st.getObject? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) with
  | error e => rw [hB] at h; simp at h
  | ok val =>
    cases val with
    | none => rfl
    | some triple => obtain ⟨tid, p, d⟩ := triple; rw [hB] at h; simp at h

/-- SM5.A.6 helper: `chooseThreadOnCore = .ok (some tid)` exposes the
selected `(tid, priority, deadline)` triple from the bucket-first scan. -/
theorem chooseThreadOnCore_eq_some_imp_bucket_some
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (h : chooseThreadOnCore st c = .ok (some tid)) :
    ∃ p d, chooseBestInBucket st.getObject? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok (some (tid, p, d)) := by
  unfold chooseThreadOnCore at h
  cases hB : chooseBestInBucket st.getObject? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) with
  | error e => rw [hB] at h; simp at h
  | ok val =>
    cases val with
    | none => rw [hB] at h; simp at h
    | some triple =>
      obtain ⟨t, tp, td⟩ := triple
      rw [hB] at h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      exact ⟨tp, td, rfl⟩

/-- SM5.A.4 helper: a `.ok` from the bucket-first scan lifts to a `.ok`
from `chooseThreadOnCore` (the wrapper only renames `some (tid, _, _)` to
`some tid`). -/
theorem chooseThreadOnCore_ok_of_bucket_ok
    (st : SystemState) (c : CoreId)
    (val : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (h : chooseBestInBucket st.getObject? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok val) :
    ∃ r, chooseThreadOnCore st c = .ok r := by
  unfold chooseThreadOnCore
  rw [h]
  cases val with
  | none => exact ⟨none, rfl⟩
  | some triple => obtain ⟨tid, p, d⟩ := triple; exact ⟨some tid, rfl⟩

/-- SM5.A.4 / SM5.A.6 helper: bridge `runnableThreadsAreTCBsOnCore` (stated
with the typed `getTcb?` accessor) to the raw `objects.get?` form the
selection fold consumes.  The two are definitionally connected through
`getTcb?_eq_some_iff` plus `RHTable[k]? = RHTable.get? k`. -/
private theorem runnableThreadsAreTCBs_objects_get?
    (st : SystemState) (c : CoreId) (hRunnable : runnableThreadsAreTCBsOnCore st c) :
    ∀ t ∈ (st.scheduler.runQueueOnCore c).toList,
      ∃ tcb : TCB, st.objects.get? t.toObjId = some (.tcb tcb) := by
  intro t ht
  obtain ⟨tcb, htcb⟩ := hRunnable t ht
  exact ⟨tcb, (SystemState.getTcb?_eq_some_iff st t tcb).mp htcb⟩

-- ── Public SM5.A.4 theorems: completeness / idle-fallback. ──

/-- WS-SM SM5.A.4: `chooseThreadOnCore` never errors on a well-formed run
queue whose every member resolves to a TCB.  The `.error` branch
(`schedulerInvariantViolation`, signalling a corrupted run queue) is
unreachable under the per-core scheduler invariant — so on any valid state
the selection returns either `.ok none` (no eligible thread → fall back to
idle) or `.ok (some tid)`.  This is the "the selection is total on valid
states" half of idle-fallback completeness. -/
theorem chooseThreadOnCore_ok_of_runnableTCBs
    (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c) :
    ∃ r, chooseThreadOnCore st c = .ok r := by
  obtain ⟨val, hbucket⟩ := chooseBestInBucket_ok_of_allTcb st.objects.get?
    (st.scheduler.runQueueOnCore c) (st.scheduler.activeDomainOnCore c) hwf
    (runnableThreadsAreTCBs_objects_get? st c hRunnable)
  exact chooseThreadOnCore_ok_of_bucket_ok st c val hbucket

/-- WS-SM SM5.A.4: completeness of selection — `chooseThreadOnCore` returns
the idle-fallback signal `.ok none` **only** when there is genuinely no
runnable thread of core `c`'s active domain in its run queue.  Equivalently:
every run-queue member is outside the active domain.  This is what makes the
idle fallback *complete* — the scheduler runs the idle thread exactly when
no domain-eligible thread is available, never dropping a runnable one. -/
theorem chooseThreadOnCore_none_no_eligible
    (st : SystemState) (c : CoreId)
    (h : chooseThreadOnCore st c = .ok none) :
    ∀ tid ∈ (st.scheduler.runQueueOnCore c).toList, ∀ tcb : TCB,
      st.getTcb? tid = some tcb →
      tcb.domain ≠ st.scheduler.activeDomainOnCore c := by
  intro tid hmem tcb htcb
  have hbucket := chooseThreadOnCore_eq_none_imp_bucket_none st c h
  have htoList := chooseBestInBucket_none_imp_toList_none st.objects.get?
    (st.scheduler.runQueueOnCore c) (st.scheduler.activeDomainOnCore c) hbucket
  have hObjGet : st.objects.get? tid.toObjId = some (.tcb tcb) :=
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp htcb
  have hElig := chooseBestRunnableBy_none_no_eligible st.objects.get?
    (fun t => t.domain == st.scheduler.activeDomainOnCore c)
    (st.scheduler.runQueueOnCore c).toList htoList tid hmem tcb hObjGet
  simpa using hElig

/-- WS-SM SM5.A.4 (idle-fallback completeness, plan §3.5.2 foundation): when
core `c`'s run queue holds a runnable thread in its active domain, the
selection succeeds with `some`.  This is the conditional form SM5.E
discharges by supplying the per-core idle thread as the always-present
in-domain candidate, yielding the unconditional
`chooseThreadOnCore_always_succeeds`. -/
theorem chooseThreadOnCore_some_of_eligible
    (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c)
    (tid₀ : SeLe4n.ThreadId) (tcb₀ : TCB)
    (hMem : tid₀ ∈ (st.scheduler.runQueueOnCore c).toList)
    (hTcb : st.getTcb? tid₀ = some tcb₀)
    (hDom : tcb₀.domain = st.scheduler.activeDomainOnCore c) :
    ∃ tid, chooseThreadOnCore st c = .ok (some tid) := by
  obtain ⟨r, hr⟩ := chooseThreadOnCore_ok_of_runnableTCBs st c hwf hRunnable
  cases r with
  | some tid => exact ⟨tid, hr⟩
  | none =>
    exact absurd hDom (chooseThreadOnCore_none_no_eligible st c hr tid₀ hMem tcb₀ hTcb)

-- ── Public SM5.A.6 theorems: selection soundness + preservation. ──

/-- WS-SM SM5.A.6 (selection soundness): a thread chosen by
`chooseThreadOnCore` is a genuine member of core `c`'s run queue.  This is
the substantive "preserves well-formedness" content for a read-only
selection: the choice respects the run queue's structure — it never invents
a thread, so the run queue's membership invariant is honoured downstream
(e.g. by `switchToThreadOnCore`'s dequeue in SM5.B). -/
theorem chooseThreadOnCore_some_mem_runQueueOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : chooseThreadOnCore st c = .ok (some tid)) :
    tid ∈ (st.scheduler.runQueueOnCore c).toList := by
  obtain ⟨p, d, hbucket⟩ := chooseThreadOnCore_eq_some_imp_bucket_some st c tid h
  exact chooseBestInBucket_result_mem st.objects.get? (st.scheduler.runQueueOnCore c)
    (st.scheduler.activeDomainOnCore c) tid p d hwf hbucket

/-- WS-SM SM5.A.6 (preservation form): the `Kernel`-monad `chooseThread` is
a pure read, so it preserves every core's run-queue well-formedness.  This
is the literal "`chooseThread` preserves `wellFormed`" statement; it follows
trivially from `chooseThread_preserves_state` (the selection threads the
state unchanged). -/
theorem chooseThread_preserves_runQueueOnCore_wellFormed
    (st st' : SystemState) (next : Option SeLe4n.ThreadId) (c : CoreId)
    (hStep : chooseThread st = .ok (next, st'))
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed) :
    (st'.scheduler.runQueueOnCore c).wellFormed := by
  rw [chooseThread_preserves_state st st' next hStep]; exact hwf

/-- WS-SM SM5.A.6 (the plan's literal `chooseThreadOnCore_preserves_wellFormed`
name): `chooseThreadOnCore` is a pure read, so it leaves core `c`'s run queue
— and hence its well-formedness — unchanged (there is no post-state to
"preserve").  The *substantive* "respects well-formedness" content is the
membership result `chooseThreadOnCore_some_mem_runQueueOnCore`; this theorem
is the plan-named anchor, bundling the (trivial) preservation of the
well-formed run queue with the (substantive) membership of the chosen
thread. -/
theorem chooseThreadOnCore_preserves_wellFormed
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : chooseThreadOnCore st c = .ok (some tid)) :
    (st.scheduler.runQueueOnCore c).wellFormed ∧
      tid ∈ (st.scheduler.runQueueOnCore c).toList :=
  ⟨hwf, chooseThreadOnCore_some_mem_runQueueOnCore st c tid hwf h⟩

-- ============================================================================
-- §3b  SM5.A.3 — Selection optimality (plan §3.1.1, Theorem 3.1.1)
-- ============================================================================

/-- WS-SM SM5.A.3 (plan §3.1.1, `chooseThreadOnCore_selects_highest`): the
selected thread is the optimal (priority / EDF-deadline / FIFO best, via
`isBetterCandidate`) eligible thread among core `c`'s **maximum-priority
bucket** — no active-domain thread in that bucket beats the selection.

**Why the maximum-priority bucket, not the whole run queue.**  The selector
`chooseBestInBucket` is bucket-first: it buckets by *effective* priority
(`threadPriority`, which under the scheduler invariant equals
`TCB.boostedPriority`, i.e. `max(base, pipBoost)`) and, within the
highest-effective-priority bucket, picks the `isBetterCandidate`-best by the
thread's *base* priority + deadline.  Because `TCB.boostedPriority ≥
base priority`, a thread in a *lower* effective bucket can have a *higher*
base priority than the selection — so a global "highest base priority over
the whole queue" claim would be **false**, and is deliberately not made here.
The faithful optimality is therefore stated over the maximum-priority bucket,
where the selection genuinely competes.  This is non-vacuous in the
bucket-success path (the selection is the bucket's best) and vacuously true
in the full-scan fallback (no active-domain thread sits in the maximum
bucket, which is exactly why the fallback fired). -/
theorem chooseThreadOnCore_selects_highest
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (selTcb : TCB)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c)
    (hSel : chooseThreadOnCore st c = .ok (some tid))
    (hSelTcb : st.getTcb? tid = some selTcb) :
    ∀ t ∈ (st.scheduler.runQueueOnCore c).maxPriorityBucket, ∀ tcb : TCB,
      st.getTcb? t = some tcb →
      tcb.domain = st.scheduler.activeDomainOnCore c →
        isBetterCandidate selTcb.priority selTcb.deadline tcb.priority tcb.deadline = false := by
  intro t ht tcb htTcb htDom
  obtain ⟨resPrio, resDl, hbucket⟩ := chooseThreadOnCore_eq_some_imp_bucket_some st c tid hSel
  have hSelObj : st.getObject? tid.toObjId = some (.tcb selTcb) :=
    (SystemState.getTcb?_eq_some_iff st tid selTcb).mp hSelTcb
  have hTObj : st.objects.get? t.toObjId = some (.tcb tcb) :=
    (SystemState.getTcb?_eq_some_iff st t tcb).mp htTcb
  have hMaxAll : ∀ u ∈ (st.scheduler.runQueueOnCore c).maxPriorityBucket,
      ∃ utcb : TCB, st.objects.get? u.toObjId = some (.tcb utcb) := by
    intro u hu
    exact runnableThreadsAreTCBs_objects_get? st c hRunnable u
      (RunQueue.membership_implies_flat _ u
        (RunQueue.maxPriorityBucket_subset _ hwf u hu))
  have hElig : (fun tc : TCB => tc.domain == st.scheduler.activeDomainOnCore c) tcb = true := by
    simp [htDom]
  rw [bucketFirst_fullScan_equivalence] at hbucket
  cases hMax : chooseBestRunnableInDomain st.getObject?
      (st.scheduler.runQueueOnCore c).maxPriorityBucket
      (st.scheduler.activeDomainOnCore c) none with
  | error e => rw [hMax] at hbucket; simp at hbucket
  | ok val =>
    cases val with
    | some r =>
      rw [hMax] at hbucket
      simp only [Except.ok.injEq, Option.some.injEq] at hbucket
      rw [hbucket] at hMax
      obtain ⟨resTcb, hResTcb, hResP, hResD⟩ :=
        chooseBestRunnableBy_result_fields st.getObject?
          (fun tc => tc.domain == st.scheduler.activeDomainOnCore c)
          (st.scheduler.runQueueOnCore c).maxPriorityBucket none tid resPrio resDl hMax
          (by intro _ _ _ h; simp at h)
      rw [hSelObj] at hResTcb; cases hResTcb
      have hOpt := chooseBestRunnableBy_optimal st.getObject?
        (fun tc => tc.domain == st.scheduler.activeDomainOnCore c)
        (st.scheduler.runQueueOnCore c).maxPriorityBucket tid resPrio resDl hMax hMaxAll
      have hNoBeat := hOpt t ht tcb hTObj hElig
      rw [hResP, hResD]
      exact hNoBeat
    | none =>
      rw [hMax] at hbucket
      have hNoElig := chooseBestRunnableBy_none_no_eligible st.objects.get?
        (fun tc => tc.domain == st.scheduler.activeDomainOnCore c)
        (st.scheduler.runQueueOnCore c).maxPriorityBucket hMax t ht tcb hTObj
      simp [htDom] at hNoElig

-- ============================================================================
-- §4  SM5.A.7 — Decidability of the selection result
-- ============================================================================

/-- WS-SM SM5.A.7: "core `c` selects `tid`" — the decidable proposition the
SM5.A unit tests discharge on concrete states by `decide`.  Its `Decidable`
instance is supplied explicitly just below (Lean core does **not** derive
`DecidableEq (Except _ _)`, so the instance cannot be `inferInstance`d; it is
discharged by structural case analysis on the evaluated selection result). -/
def chooseThreadOnCoreSelects (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : Prop :=
  chooseThreadOnCore st c = .ok (some tid)

/-- WS-SM SM5.A.7: `chooseThreadOnCoreSelects` is decidable.  Lean core does
not derive `DecidableEq (Except _ _)`, so the instance is discharged by a
structural case analysis on the (fully-evaluated) selection result rather
than by `inferInstance`. -/
instance (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    Decidable (chooseThreadOnCoreSelects st c tid) :=
  match h : chooseThreadOnCore st c with
  | .ok (some t) =>
      if ht : t = tid then .isTrue (by simp [chooseThreadOnCoreSelects, h, ht])
      else .isFalse (by simp [chooseThreadOnCoreSelects, h, ht])
  | .ok none => .isFalse (by simp [chooseThreadOnCoreSelects, h])
  | .error e => .isFalse (by simp [chooseThreadOnCoreSelects, h])

/-- WS-SM SM5.A.7: "core `c` has no domain-eligible thread, so its scheduler
must fall back to idle" — the decidable complement of
`chooseThreadOnCoreSelects`. -/
def chooseThreadOnCoreIdleFallback (st : SystemState) (c : CoreId) : Prop :=
  chooseThreadOnCore st c = .ok none

instance (st : SystemState) (c : CoreId) :
    Decidable (chooseThreadOnCoreIdleFallback st c) :=
  match h : chooseThreadOnCore st c with
  | .ok none => .isTrue (by simp [chooseThreadOnCoreIdleFallback, h])
  | .ok (some t) => .isFalse (by simp [chooseThreadOnCoreIdleFallback, h])
  | .error e => .isFalse (by simp [chooseThreadOnCoreIdleFallback, h])

/-- WS-SM SM5.A.7 (budget variant): "core `c`'s budget-aware selection picks
`tid`". -/
def chooseThreadEffectiveOnCoreSelects (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : Prop :=
  chooseThreadEffectiveOnCore st c = .ok (some tid)

instance (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    Decidable (chooseThreadEffectiveOnCoreSelects st c tid) :=
  match h : chooseThreadEffectiveOnCore st c with
  | .ok (some t) =>
      if ht : t = tid then .isTrue (by simp [chooseThreadEffectiveOnCoreSelects, h, ht])
      else .isFalse (by simp [chooseThreadEffectiveOnCoreSelects, h, ht])
  | .ok none => .isFalse (by simp [chooseThreadEffectiveOnCoreSelects, h])
  | .error e => .isFalse (by simp [chooseThreadEffectiveOnCoreSelects, h])

/-- WS-SM SM5.A.7 (budget variant): "core `c`'s budget-aware selection finds no
in-budget in-domain thread, so it falls back to idle". -/
def chooseThreadEffectiveOnCoreIdleFallback (st : SystemState) (c : CoreId) : Prop :=
  chooseThreadEffectiveOnCore st c = .ok none

instance (st : SystemState) (c : CoreId) :
    Decidable (chooseThreadEffectiveOnCoreIdleFallback st c) :=
  match h : chooseThreadEffectiveOnCore st c with
  | .ok none => .isTrue (by simp [chooseThreadEffectiveOnCoreIdleFallback, h])
  | .ok (some t) => .isFalse (by simp [chooseThreadEffectiveOnCoreIdleFallback, h])
  | .error e => .isFalse (by simp [chooseThreadEffectiveOnCoreIdleFallback, h])

-- ============================================================================
-- §5  Corollaries via the SM4.C aggregate `schedulerInvariant_perCore`
-- ============================================================================

/-- WS-SM SM5.A.4 (plan §3.5.2 form): under the aggregate per-core scheduler
invariant, `chooseThreadOnCore` never errors.  Discharges the well-formed +
runnable-are-TCBs hypotheses of `chooseThreadOnCore_ok_of_runnableTCBs` from
`schedulerInvariant_perCore`. -/
theorem chooseThreadOnCore_ok_of_schedulerInvariant
    (st : SystemState) (c : CoreId) (h : schedulerInvariant_perCore st c) :
    ∃ r, chooseThreadOnCore st c = .ok r :=
  chooseThreadOnCore_ok_of_runnableTCBs st c
    (schedulerInvariant_perCore_to_runQueueOnCoreWellFormed h)
    (schedulerInvariant_perCore_to_runnableThreadsAreTCBs h)

/-- WS-SM SM5.A.6 (plan §3.5.2 form): under the aggregate per-core scheduler
invariant, a chosen thread is a genuine run-queue member. -/
theorem chooseThreadOnCore_some_mem_of_schedulerInvariant
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : schedulerInvariant_perCore st c)
    (h : chooseThreadOnCore st c = .ok (some tid)) :
    tid ∈ (st.scheduler.runQueueOnCore c).toList :=
  chooseThreadOnCore_some_mem_runQueueOnCore st c tid
    (schedulerInvariant_perCore_to_runQueueOnCoreWellFormed hInv) h

-- ============================================================================
-- §6  Budget-aware per-core selection (`chooseThreadEffectiveOnCore`)
-- ============================================================================
--
-- `chooseThreadEffectiveOnCore` (in `Selection.lean`) is the CBS-budget-aware
-- companion to `chooseThreadOnCore`: it additionally rejects threads whose
-- SchedContext budget is exhausted (`hasSufficientBudget`).  This section
-- mirrors the SM5.A theorems for it: per-core independence, non-erroring,
-- completeness, selection soundness, and — the property unique to the
-- budget-aware variant — that a *selected* thread genuinely has budget.

/-- SM5.A budget helper: the effective fold over a list of genuine TCBs never
errors. -/
theorem chooseBestRunnableEffective_ok_of_allTcb
    (st : SystemState) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)),
      (∀ t ∈ list, ∃ tcb : TCB, st.objects.get? t.toObjId = some (.tcb tcb)) →
      ∃ r, chooseBestRunnableEffective st eligible list best = .ok r := by
  intro list
  induction list with
  | nil => intro best _; exact ⟨best, rfl⟩
  | cons hd tl ih =>
    intro best hAll
    obtain ⟨hdTcb, hHdObj⟩ := hAll hd (List.mem_cons_self ..)
    have hAllTl : ∀ t ∈ tl, ∃ tcb : TCB, st.objects.get? t.toObjId = some (.tcb tcb) :=
      fun t ht => hAll t (List.mem_cons_of_mem _ ht)
    unfold chooseBestRunnableEffective
    rw [show st.getTcb? hd = some hdTcb from
      (SeLe4n.Model.SystemState.getTcb?_eq_some_iff st hd hdTcb).mpr hHdObj]
    exact ih _ hAllTl

/-- SM5.A budget helper: `hasSufficientBudget` reads the state only through
the object store, so two states with equal `objects` agree on it. -/
theorem hasSufficientBudget_objects_congr (s₁ s₂ : SystemState) (tcb : TCB)
    (h : s₁.objects = s₂.objects) :
    hasSufficientBudget s₁ tcb = hasSufficientBudget s₂ tcb := by
  unfold hasSufficientBudget SystemState.getSchedContext?
  rw [h]

/-- SM5.A budget helper: `resolveEffectivePrioDeadline` reads the state only
through the object store, so two states with equal `objects` agree on it. -/
theorem resolveEffectivePrioDeadline_objects_congr (s₁ s₂ : SystemState) (tcb : TCB)
    (h : s₁.objects = s₂.objects) :
    resolveEffectivePrioDeadline s₁ tcb = resolveEffectivePrioDeadline s₂ tcb := by
  unfold resolveEffectivePrioDeadline SystemState.getSchedContext?
  rw [h]

/-- SM5.A budget helper: the effective fold reads the state only through the
object store (the run queue / active domain enter as explicit arguments), so
two states with equal `objects` produce identical folds.  This is the
congruence that makes the budget-aware per-core selection frameable. -/
theorem chooseBestRunnableEffective_objects_congr (s₁ s₂ : SystemState)
    (eligible : TCB → Bool) (h : s₁.objects = s₂.objects) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)),
      chooseBestRunnableEffective s₁ eligible list best
        = chooseBestRunnableEffective s₂ eligible list best := by
  intro list
  induction list with
  | nil => intro best; rfl
  | cons hd tl ih =>
    intro best
    have h' : s₂.objects = s₁.objects := h.symm
    -- The fold reads the store through `getTcb?`, and that accessor depends on
    -- the state only through `objects`, so the two sides agree on it outright.
    have hTcb : s₁.getTcb? hd = s₂.getTcb? hd := by
      unfold SeLe4n.Model.SystemState.getTcb?; rw [h]
    cases hObj : s₁.getTcb? hd with
    | none =>
      have hObj2 : s₂.getTcb? hd = none := by rw [← hTcb]; exact hObj
      -- Round 15: both sides skip the entry, so both reduce to the tail fold.
      unfold chooseBestRunnableEffective
      simp only [hObj, hObj2]
      exact ih _
    | some tcb =>
      have hObj2 : s₂.getTcb? hd = some tcb := by rw [← hTcb]; exact hObj
      unfold chooseBestRunnableEffective
      simp only [hObj, hObj2, hasSufficientBudget_objects_congr s₁ s₂ tcb h,
        resolveEffectivePrioDeadline_objects_congr s₁ s₂ tcb h]
      exact ih _

/-- SM5.A budget helper: the bucket-first effective selector is objects-only
dependent. -/
theorem chooseBestInBucketEffective_objects_congr (s₁ s₂ : SystemState)
    (rq : RunQueue) (ad : SeLe4n.DomainId) (h : s₁.objects = s₂.objects) :
    chooseBestInBucketEffective s₁ rq ad = chooseBestInBucketEffective s₂ rq ad := by
  unfold chooseBestInBucketEffective chooseBestRunnableInDomainEffective
  simp only [chooseBestRunnableEffective_objects_congr s₁ s₂ (fun tcb => tcb.domain == ad) h]

/-- WS-SM SM5.A.3 (budget variant, frame form): `chooseThreadEffectiveOnCore`'s
read footprint on core `c` is `(objects, runQueueOnCore c, activeDomainOnCore
c)`.  Unlike the non-budget `chooseThreadOnCore_frame`, full `objects` equality
is genuinely required (not just a lookup function) because the budget check and
effective-priority resolution traverse SchedContexts in the object store. -/
theorem chooseThreadEffectiveOnCore_frame (s₁ s₂ : SystemState) (c : CoreId)
    (hObj : s₁.objects = s₂.objects)
    (hRQ : s₁.scheduler.runQueueOnCore c = s₂.scheduler.runQueueOnCore c)
    (hAD : s₁.scheduler.activeDomainOnCore c = s₂.scheduler.activeDomainOnCore c) :
    chooseThreadEffectiveOnCore s₁ c = chooseThreadEffectiveOnCore s₂ c := by
  unfold chooseThreadEffectiveOnCore
  rw [hRQ, hAD, chooseBestInBucketEffective_objects_congr s₁ s₂ _ _ hObj]

/-- WS-SM SM5.A.3 (budget variant): per-core independence under a sibling-core
run-queue write.  Writing core `c'`'s run queue (`c' ≠ c`) leaves
`chooseThreadEffectiveOnCore · c` unchanged. -/
theorem chooseThreadEffectiveOnCore_independent_of_setRunQueueOnCore
    (s : SystemState) (c c' : CoreId) (rq : RunQueue) (h : c ≠ c') :
    chooseThreadEffectiveOnCore
        { s with scheduler := s.scheduler.setRunQueueOnCore c' rq } c
      = chooseThreadEffectiveOnCore s c := by
  apply chooseThreadEffectiveOnCore_frame
  · rfl
  · exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne s.scheduler c' c rq (Ne.symm h)
  · exact SchedulerState.setRunQueueOnCore_activeDomainOnCore s.scheduler c' c rq

/-- SM5.A budget helper: the bucket-first effective selector unfolds to "scan
the max-priority bucket, then fall back to a full-list scan" (the effective
analogue of `bucketFirst_fullScan_equivalence`).  Stated as a `rfl`-lemma so
the explicit match form is `rw`-able (a raw `unfold` produces a compiled match
whose scrutinee is not rewritable). -/
theorem bucketFirstEffective_fullScan_equivalence
    (st : SystemState) (rq : RunQueue) (ad : SeLe4n.DomainId) :
    chooseBestInBucketEffective st rq ad =
      (match chooseBestRunnableInDomainEffective st rq.maxPriorityBucket ad none with
       | .error e => .error e
       | .ok (some result) => .ok (some result)
       | .ok none => chooseBestRunnableInDomainEffective st rq.toList ad none) := rfl

/-- SM5.A budget helper: a recorded candidate of the effective fold (from any
`best`) either is a genuine member of the scanned list that **passed both the
domain-eligibility and the budget filter**, or was already the recorded
`best`.  Specialised to `best = none` below for the budget-soundness +
selection-soundness results. -/
private theorem chooseBestRunnableEffective_result_props_aux
    (st : SystemState) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
      (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline),
      chooseBestRunnableEffective st eligible list best = .ok (some (rt, rp, rd)) →
      (rt ∈ list ∧ ∃ rtcb : TCB, st.objects.get? rt.toObjId = some (.tcb rtcb)
          ∧ eligible rtcb = true ∧ hasSufficientBudget st rtcb = true)
        ∨ (∃ p d, best = some (rt, p, d)) := by
  intro list
  induction list with
  | nil =>
    intro best rt rp rd h
    simp only [chooseBestRunnableEffective] at h
    exact Or.inr ⟨rp, rd, by rw [Except.ok.injEq] at h; rw [h]⟩
  | cons hd tl ih =>
    intro best rt rp rd h
    unfold chooseBestRunnableEffective at h
    cases hObj : st.getTcb? hd with
    -- Round 15: a head that is not a TCB — absent, or stored under another
    -- kind, which `getTcb?` answers `none` for alike — is skipped with `best`
    -- untouched, so both outcomes carry over from the tail unchanged.
    | none =>
      rw [hObj] at h
      rcases ih _ rt rp rd h with hprops | hb
      · exact Or.inl ⟨List.mem_cons_of_mem _ hprops.1, hprops.2⟩
      · exact Or.inr hb
    | some tcb =>
      -- The conclusion is phrased over the raw store read, so the accessor's
      -- answer is converted once, here, rather than at each use.
      have hObjRaw : st.objects.get? hd.toObjId = some (.tcb tcb) :=
        (SeLe4n.Model.SystemState.getTcb?_eq_some_iff st hd tcb).mp hObj
      · rw [hObj] at h
        by_cases hCond : (eligible tcb && hasSufficientBudget st tcb) = true
        · obtain ⟨hEl, hBu⟩ := And.intro
            (by simpa using (Bool.and_eq_true _ _ ▸ hCond).1)
            (by simpa using (Bool.and_eq_true _ _ ▸ hCond).2)
          -- recorded path: best' records `hd` (when it beats `best`) or keeps `best`.
          cases best with
          | none =>
            simp only [hCond, if_true] at h
            rcases ih _ rt rp rd h with hprops | ⟨p, d, hb⟩
            · exact Or.inl ⟨List.mem_cons_of_mem _ hprops.1, hprops.2⟩
            · simp only [Option.some.injEq, Prod.mk.injEq] at hb
              exact Or.inl ⟨List.mem_cons.mpr (Or.inl hb.1.symm),
                tcb, hb.1.symm ▸ hObjRaw, hEl, hBu⟩
          | some y =>
            obtain ⟨yt, yp, yd⟩ := y
            by_cases hBetter : isBetterCandidate yp yd
                (resolveEffectivePrioDeadline st tcb).1 (resolveEffectivePrioDeadline st tcb).2
            · simp only [hCond, if_true, hBetter] at h
              rcases ih _ rt rp rd h with hprops | ⟨p, d, hb⟩
              · exact Or.inl ⟨List.mem_cons_of_mem _ hprops.1, hprops.2⟩
              · simp only [Option.some.injEq, Prod.mk.injEq] at hb
                exact Or.inl ⟨List.mem_cons.mpr (Or.inl hb.1.symm),
                  tcb, hb.1.symm ▸ hObjRaw, hEl, hBu⟩
            · simp only [hCond, if_true, hBetter] at h
              rcases ih _ rt rp rd h with hprops | hb
              · exact Or.inl ⟨List.mem_cons_of_mem _ hprops.1, hprops.2⟩
              · exact Or.inr hb
        · simp only [Bool.not_eq_true] at hCond
          simp only [hCond] at h
          rcases ih _ rt rp rd h with hprops | hb
          · exact Or.inl ⟨List.mem_cons_of_mem _ hprops.1, hprops.2⟩
          · exact Or.inr hb

/-- SM5.A budget helper: a `none`-seeded effective scan that selects `rt`
witnesses that `rt` is a member of the scanned list, resolves to a TCB, and
passed both the domain-eligibility and the CBS budget filter. -/
theorem chooseBestRunnableEffective_result_props
    (st : SystemState) (eligible : TCB → Bool) (list : List SeLe4n.ThreadId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (h : chooseBestRunnableEffective st eligible list none = .ok (some (rt, rp, rd))) :
    rt ∈ list ∧ ∃ rtcb : TCB, st.objects.get? rt.toObjId = some (.tcb rtcb)
      ∧ eligible rtcb = true ∧ hasSufficientBudget st rtcb = true := by
  rcases chooseBestRunnableEffective_result_props_aux st eligible list none rt rp rd h with
    hp | ⟨_, _, hb⟩
  · exact hp
  · exact absurd hb (by simp)

/-- WS-SM SM5.I (PR-B): the effective analogue of `chooseBestRunnableBy_result_fields`.
The result's recorded `(priority, deadline)` is the *effective* priority/deadline
(`resolveEffectivePrioDeadline`) of the selected thread.  Needed to connect the
budget-aware selection's stored priority/deadline back to the selected TCB's
effective scheduling parameters (the budget-EDF predicate). -/
theorem chooseBestRunnableEffective_result_fields
    (st : SystemState) (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (init : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableEffective st eligible runnable init =
      .ok (some (resTid, resPrio, resDl)))
    (hInit : ∀ iTid iPrio iDl, init = some (iTid, iPrio, iDl) →
      ∃ itcb, st.objects.get? iTid.toObjId = some (.tcb itcb) ∧
        (resolveEffectivePrioDeadline st itcb).1 = iPrio ∧
        (resolveEffectivePrioDeadline st itcb).2 = iDl) :
    ∃ tcb, st.objects.get? resTid.toObjId = some (.tcb tcb) ∧
      (resolveEffectivePrioDeadline st tcb).1 = resPrio ∧
      (resolveEffectivePrioDeadline st tcb).2 = resDl := by
  induction runnable generalizing init with
  | nil =>
      unfold chooseBestRunnableEffective at hOk
      simp at hOk; cases hOk
      exact hInit resTid resPrio resDl rfl
  | cons hd tl ih =>
      unfold chooseBestRunnableEffective at hOk
      cases hHd : st.getTcb? hd with
      -- Round 15: a head that is not a TCB is skipped with `init` untouched.
      | none => rw [hHd] at hOk; exact ih init hOk hInit
      | some hdTcb =>
          have hHdObj : st.objects.get? hd.toObjId = some (.tcb hdTcb) :=
            (SeLe4n.Model.SystemState.getTcb?_eq_some_iff st hd hdTcb).mp hHd
          rw [hHd] at hOk
          by_cases hCond : (eligible hdTcb && hasSufficientBudget st hdTcb) = true
          · cases init with
            | none =>
                simp only [hCond, if_true] at hOk
                refine ih (some (hd, (resolveEffectivePrioDeadline st hdTcb).1,
                  (resolveEffectivePrioDeadline st hdTcb).2)) hOk ?_
                intro iTid iPrio iDl hEq
                simp only [Option.some.injEq, Prod.mk.injEq] at hEq
                obtain ⟨rfl, rfl, rfl⟩ := hEq
                exact ⟨hdTcb, hHdObj, rfl, rfl⟩
            | some triple =>
                obtain ⟨initTid, initPrio, initDl⟩ := triple
                by_cases hBeat : isBetterCandidate initPrio initDl
                    (resolveEffectivePrioDeadline st hdTcb).1
                    (resolveEffectivePrioDeadline st hdTcb).2
                · simp only [hCond, if_true, hBeat] at hOk
                  refine ih (some (hd, (resolveEffectivePrioDeadline st hdTcb).1,
                    (resolveEffectivePrioDeadline st hdTcb).2)) hOk ?_
                  intro iTid iPrio iDl hEq
                  simp only [Option.some.injEq, Prod.mk.injEq] at hEq
                  obtain ⟨rfl, rfl, rfl⟩ := hEq
                  exact ⟨hdTcb, hHdObj, rfl, rfl⟩
                · simp only [hCond, if_true, hBeat] at hOk
                  exact ih (some (initTid, initPrio, initDl)) hOk hInit
          · rw [Bool.not_eq_true] at hCond
            simp only [hCond, Bool.false_eq_true, if_false] at hOk
            exact ih init hOk hInit

/-- WS-SM SM5.I (PR-B): the effective analogue of `chooseBestRunnableBy_optimal_combined`.
The budget-aware `none`-or-`init`-seeded effective scan's result is not
`isBetterCandidate`-beaten by any scanned domain-eligible thread that has
sufficient budget (compared on *effective* `resolveEffectivePrioDeadline`
priority/deadline), nor by the seed.  Mirrors the non-budget proof with the
`&& hasSufficientBudget` filter; the `let (prio, dl) := resolveEffectivePrioDeadline`
binding is zeta-reduced to `.1` / `.2` projections by `simp`. -/
private theorem chooseBestRunnableEffective_optimal_combined
    (st : SystemState) (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (init : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableEffective st eligible runnable init =
           .ok (some (resTid, resPrio, resDl)))
    (hAllTcb : ∀ t, t ∈ runnable → ∃ tcb, st.objects.get? t.toObjId = some (.tcb tcb)) :
    (∀ t, t ∈ runnable →
      ∀ tcb, st.objects.get? t.toObjId = some (.tcb tcb) →
        eligible tcb = true → hasSufficientBudget st tcb = true →
          isBetterCandidate resPrio resDl
            (resolveEffectivePrioDeadline st tcb).1
            (resolveEffectivePrioDeadline st tcb).2 = false) ∧
    (∀ initTid ip id, init = some (initTid, ip, id) →
       isBetterCandidate resPrio resDl ip id = false) := by
  induction runnable generalizing init with
  | nil =>
    simp [chooseBestRunnableEffective] at hOk
    constructor
    · intro t hMem; simp at hMem
    · intro initTid ip id hInit; subst hOk; cases hInit
      exact isBetterCandidate_irrefl resPrio resDl
  | cons hd tl ih =>
    unfold chooseBestRunnableEffective at hOk
    have hAllTl : ∀ t, t ∈ tl → ∃ tcb, st.objects.get? t.toObjId = some (.tcb tcb) :=
      fun t hMem => hAllTcb t (List.mem_cons.mpr (Or.inr hMem))
    obtain ⟨hdTcb, hHdObj⟩ := hAllTcb hd (List.mem_cons.mpr (Or.inl rfl))
    rw [show st.getTcb? hd = some hdTcb from
      (SeLe4n.Model.SystemState.getTcb?_eq_some_iff st hd hdTcb).mpr hHdObj] at hOk
    cases hEligB : (eligible hdTcb && hasSufficientBudget st hdTcb) with
    | false =>
      simp only [hEligB] at hOk
      have ⟨ihP1, ihP2⟩ := ih init hOk hAllTl
      refine ⟨?_, ihP2⟩
      intro t hMem tcb hObj hE hB
      simp only [List.mem_cons] at hMem
      rcases hMem with h_eq | hTl
      · have h1 : st.objects.get? hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
        rw [hHdObj] at h1; cases h1
        simp [hE, hB] at hEligB
      · exact ihP1 t hTl tcb hObj hE hB
    | true =>
      simp only [hEligB, ↓reduceIte] at hOk
      cases init with
      | none =>
        have ⟨ihP1, ihP2⟩ := ih (some (hd, (resolveEffectivePrioDeadline st hdTcb).1,
          (resolveEffectivePrioDeadline st hdTcb).2)) hOk hAllTl
        refine ⟨?_, ?_⟩
        · intro t hMem tcb hObj hE hB
          simp only [List.mem_cons] at hMem
          rcases hMem with h_eq | hTl
          · have h1 : st.objects.get? hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
            rw [hHdObj] at h1; cases h1
            exact ihP2 hd _ _ rfl
          · exact ihP1 t hTl tcb hObj hE hB
        · intro _ ip id hNone; cases hNone
      | some triple =>
        obtain ⟨initTid, initPrio, initDl⟩ := triple
        dsimp only at hOk
        cases hBeatB : isBetterCandidate initPrio initDl
            (resolveEffectivePrioDeadline st hdTcb).1
            (resolveEffectivePrioDeadline st hdTcb).2 with
        | true =>
          simp only [hBeatB, ite_true] at hOk
          have ⟨ihP1, ihP2⟩ := ih (some (hd, (resolveEffectivePrioDeadline st hdTcb).1,
            (resolveEffectivePrioDeadline st hdTcb).2)) hOk hAllTl
          refine ⟨?_, ?_⟩
          · intro t hMem tcb hObj hE hB
            simp only [List.mem_cons] at hMem
            rcases hMem with h_eq | hTl
            · have h1 : st.objects.get? hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
              rw [hHdObj] at h1; cases h1
              exact ihP2 hd _ _ rfl
            · exact ihP1 t hTl tcb hObj hE hB
          · intro _ ip id hSome; cases hSome
            have hHdNoBetter := ihP2 hd _ _ rfl
            cases hResVsInit : isBetterCandidate resPrio resDl initPrio initDl with
            | false => rfl
            | true =>
              exact absurd (isBetterCandidate_transitive resPrio initPrio
                  (resolveEffectivePrioDeadline st hdTcb).1
                  resDl initDl (resolveEffectivePrioDeadline st hdTcb).2
                  hResVsInit hBeatB) (by rw [hHdNoBetter]; decide)
        | false =>
          simp only [hBeatB] at hOk
          have ⟨ihP1, ihP2⟩ := ih (some (initTid, initPrio, initDl)) hOk hAllTl
          refine ⟨?_, ihP2⟩
          intro t hMem tcb hObj hE hB
          simp only [List.mem_cons] at hMem
          rcases hMem with h_eq | hTl
          · have h1 : st.objects.get? hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
            rw [hHdObj] at h1; cases h1
            exact isBetterCandidate_not_better_trans
              (resolveEffectivePrioDeadline st hdTcb).1 initPrio resPrio
              (resolveEffectivePrioDeadline st hdTcb).2 initDl resDl
              hBeatB (ihP2 initTid initPrio initDl rfl)
          · exact ihP1 t hTl tcb hObj hE hB

/-- WS-SM SM5.I (PR-B): budget-aware selection optimality (init = none).  No
domain-eligible, budget-sufficient thread in the scanned list beats the
selected result on effective `resolveEffectivePrioDeadline` priority/deadline.
The effective analogue of `chooseBestRunnableBy_optimal`. -/
theorem chooseBestRunnableEffective_optimal
    (st : SystemState) (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableEffective st eligible runnable none =
      .ok (some (resTid, resPrio, resDl)))
    (hAllTcb : ∀ t, t ∈ runnable → ∃ tcb, st.objects.get? t.toObjId = some (.tcb tcb)) :
    ∀ t, t ∈ runnable →
      ∀ tcb, st.objects.get? t.toObjId = some (.tcb tcb) →
        eligible tcb = true → hasSufficientBudget st tcb = true →
          isBetterCandidate resPrio resDl
            (resolveEffectivePrioDeadline st tcb).1
            (resolveEffectivePrioDeadline st tcb).2 = false :=
  (chooseBestRunnableEffective_optimal_combined st eligible runnable none
    resTid resPrio resDl hOk hAllTcb).1

/-- SM5.A budget helper: a selected candidate of the bucket-first effective
scan over a well-formed run queue is a genuine run-queue member that is
in-domain and has sufficient budget. -/
theorem chooseBestInBucketEffective_result_props
    (st : SystemState) (rq : RunQueue) (ad : SeLe4n.DomainId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (hwf : rq.wellFormed)
    (h : chooseBestInBucketEffective st rq ad = .ok (some (rt, rp, rd))) :
    rt ∈ rq.toList ∧ ∃ rtcb : TCB, st.objects.get? rt.toObjId = some (.tcb rtcb)
      ∧ rtcb.domain = ad ∧ hasSufficientBudget st rtcb = true := by
  rw [bucketFirstEffective_fullScan_equivalence] at h
  cases hMax : chooseBestRunnableInDomainEffective st rq.maxPriorityBucket ad none with
  | error e => rw [hMax] at h; simp at h
  | ok val =>
    cases val with
    | some r =>
      rw [hMax] at h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      rw [h] at hMax
      obtain ⟨hMem, rtcb, hObj, hElig, hBudget⟩ :=
        chooseBestRunnableEffective_result_props st (fun tc => tc.domain == ad)
          rq.maxPriorityBucket rt rp rd hMax
      exact ⟨RunQueue.membership_implies_flat rq rt
          (RunQueue.maxPriorityBucket_subset rq hwf rt hMem),
        rtcb, hObj, eq_of_beq hElig, hBudget⟩
    | none =>
      rw [hMax] at h
      obtain ⟨hMem, rtcb, hObj, hElig, hBudget⟩ :=
        chooseBestRunnableEffective_result_props st (fun tc => tc.domain == ad)
          rq.toList rt rp rd h
      exact ⟨hMem, rtcb, hObj, eq_of_beq hElig, hBudget⟩

/-- SM5.A budget helper: `chooseThreadEffectiveOnCore = .ok (some tid)` exposes
the selected `(tid, priority, deadline)` triple. -/
theorem chooseThreadEffectiveOnCore_eq_some_imp_bucket_some
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (h : chooseThreadEffectiveOnCore st c = .ok (some tid)) :
    ∃ p d, chooseBestInBucketEffective st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok (some (tid, p, d)) := by
  unfold chooseThreadEffectiveOnCore at h
  cases hB : chooseBestInBucketEffective st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) with
  | error e => rw [hB] at h; simp at h
  | ok val =>
    cases val with
    | none => rw [hB] at h; simp at h
    | some triple =>
      obtain ⟨t, tp, td⟩ := triple
      rw [hB] at h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      exact ⟨tp, td, rfl⟩

/-- SM5.A budget helper: a `.ok` bucket-first effective scan lifts to a `.ok`
from `chooseThreadEffectiveOnCore`. -/
theorem chooseThreadEffectiveOnCore_ok_of_bucket_ok
    (st : SystemState) (c : CoreId)
    (val : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (h : chooseBestInBucketEffective st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok val) :
    ∃ r, chooseThreadEffectiveOnCore st c = .ok r := by
  unfold chooseThreadEffectiveOnCore
  rw [h]
  cases val with
  | none => exact ⟨none, rfl⟩
  | some triple => obtain ⟨tid, p, d⟩ := triple; exact ⟨some tid, rfl⟩

/-- SM5.A budget helper: the bucket-first effective scan never errors on a
well-formed all-TCB run queue. -/
theorem chooseBestInBucketEffective_ok_of_allTcb
    (st : SystemState) (rq : RunQueue) (ad : SeLe4n.DomainId)
    (hwf : rq.wellFormed)
    (hAll : ∀ t ∈ rq.toList, ∃ tcb : TCB, st.objects.get? t.toObjId = some (.tcb tcb)) :
    ∃ val, chooseBestInBucketEffective st rq ad = .ok val := by
  have hMaxAll : ∀ t ∈ rq.maxPriorityBucket, ∃ tcb : TCB,
      st.objects.get? t.toObjId = some (.tcb tcb) := by
    intro t ht
    exact hAll t (RunQueue.membership_implies_flat rq t
      (RunQueue.maxPriorityBucket_subset rq hwf t ht))
  obtain ⟨maxVal, hMax⟩ :
      ∃ r, chooseBestRunnableInDomainEffective st rq.maxPriorityBucket ad none = .ok r :=
    chooseBestRunnableEffective_ok_of_allTcb st (fun tc => tc.domain == ad)
      rq.maxPriorityBucket none hMaxAll
  rw [bucketFirstEffective_fullScan_equivalence, hMax]
  cases maxVal with
  | some r => exact ⟨some r, rfl⟩
  | none =>
    exact chooseBestRunnableEffective_ok_of_allTcb st (fun tc => tc.domain == ad)
      rq.toList none hAll

-- ── Public budget-aware theorems. ──

/-- WS-SM SM5.A.4 (budget variant): `chooseThreadEffectiveOnCore` never errors
on a well-formed all-TCB run queue. -/
theorem chooseThreadEffectiveOnCore_ok_of_runnableTCBs
    (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c) :
    ∃ r, chooseThreadEffectiveOnCore st c = .ok r := by
  obtain ⟨val, hbucket⟩ := chooseBestInBucketEffective_ok_of_allTcb st
    (st.scheduler.runQueueOnCore c) (st.scheduler.activeDomainOnCore c) hwf
    (runnableThreadsAreTCBs_objects_get? st c hRunnable)
  exact chooseThreadEffectiveOnCore_ok_of_bucket_ok st c val hbucket

/-- WS-SM SM5.A.6 (budget variant, selection soundness): a thread chosen by
`chooseThreadEffectiveOnCore` is a genuine member of core `c`'s run queue. -/
theorem chooseThreadEffectiveOnCore_some_mem_runQueueOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : chooseThreadEffectiveOnCore st c = .ok (some tid)) :
    tid ∈ (st.scheduler.runQueueOnCore c).toList := by
  obtain ⟨p, d, hbucket⟩ := chooseThreadEffectiveOnCore_eq_some_imp_bucket_some st c tid h
  exact (chooseBestInBucketEffective_result_props st (st.scheduler.runQueueOnCore c)
    (st.scheduler.activeDomainOnCore c) tid p d hwf hbucket).1

/-- WS-SM SM5.A (budget variant — the property unique to the budget-aware
selector): a thread chosen by `chooseThreadEffectiveOnCore` genuinely has
**sufficient CBS budget** (and is in core `c`'s active domain).  This is the
soundness of the budget filter — the whole reason the budget-aware variant
exists: it never dispatches a thread whose SchedContext budget is exhausted. -/
theorem chooseThreadEffectiveOnCore_selected_has_budget
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : chooseThreadEffectiveOnCore st c = .ok (some tid)) :
    ∃ tcb : TCB, st.getTcb? tid = some tcb
      ∧ hasSufficientBudget st tcb = true
      ∧ tcb.domain = st.scheduler.activeDomainOnCore c := by
  obtain ⟨p, d, hbucket⟩ := chooseThreadEffectiveOnCore_eq_some_imp_bucket_some st c tid h
  obtain ⟨_hMem, rtcb, hObj, hDom, hBudget⟩ :=
    chooseBestInBucketEffective_result_props st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) tid p d hwf hbucket
  exact ⟨rtcb, (SystemState.getTcb?_eq_some_iff st tid rtcb).mpr hObj, hBudget, hDom⟩

-- ── Budget-aware completeness. ──

/-- SM5.A budget helper: once the effective fold has recorded a candidate it
never returns `.ok none`. -/
theorem chooseBestRunnableEffective_some_ne_ok_none
    (st : SystemState) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (x : SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline),
      chooseBestRunnableEffective st eligible list (some x) ≠ .ok none := by
  intro list
  induction list with
  | nil => intro x h; simp [chooseBestRunnableEffective] at h
  | cons hd tl ih =>
    intro x h
    obtain ⟨xt, xp, xd⟩ := x
    unfold chooseBestRunnableEffective at h
    cases hObj : st.getTcb? hd with
    -- Round 15: skipped, so the incumbent carries into the tail.  A head that
    -- is absent and one stored under another kind are one arm here, which is
    -- what the accessor decides once.
    | none => rw [hObj] at h; exact ih _ h
    | some tcb =>
      rw [hObj] at h
      by_cases hCond : (eligible tcb && hasSufficientBudget st tcb) = true
      · simp only [hCond, if_true] at h
        split at h <;> exact ih _ h
      · simp only [Bool.not_eq_true] at hCond
        simp only [hCond] at h; exact ih _ h

/-- SM5.A budget helper: a `none`-seeded effective scan returning `.ok none`
witnesses that **no** scanned TCB was both domain-eligible and had sufficient
budget. -/
theorem chooseBestRunnableEffective_none_no_eligible
    (st : SystemState) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId),
      chooseBestRunnableEffective st eligible list none = .ok none →
      ∀ tid ∈ list, ∀ tcb : TCB,
        st.objects.get? tid.toObjId = some (.tcb tcb) →
        (eligible tcb && hasSufficientBudget st tcb) = false := by
  intro list
  induction list with
  | nil => intro _ tid hmem; simp at hmem
  | cons hd tl ih =>
    intro h tid hmem tcb hObjTid
    have hHdReduce := h
    unfold chooseBestRunnableEffective at hHdReduce
    rcases List.mem_cons.mp hmem with hEq | hMemTl
    · subst hEq
      rw [show st.getTcb? tid = some tcb from
        (SeLe4n.Model.SystemState.getTcb?_eq_some_iff st tid tcb).mpr hObjTid] at hHdReduce
      by_cases hCond : (eligible tcb && hasSufficientBudget st tcb) = true
      · exfalso
        simp only [hCond, if_true] at hHdReduce
        exact chooseBestRunnableEffective_some_ne_ok_none st eligible tl _ hHdReduce
      · simpa using hCond
    · cases hHd : st.getTcb? hd with
      -- Round 15: a head that is not a TCB is skipped, leaving the same
      -- `none`-seeded fold over the tail, so the inductive hypothesis applies
      -- directly.
      | none => rw [hHd] at hHdReduce; exact ih hHdReduce tid hMemTl tcb hObjTid
      | some hdTcb =>
        rw [hHd] at hHdReduce
        by_cases hHdCond : (eligible hdTcb && hasSufficientBudget st hdTcb) = true
        · exfalso
          simp only [hHdCond, if_true] at hHdReduce
          exact chooseBestRunnableEffective_some_ne_ok_none st eligible tl _ hHdReduce
        · simp only [Bool.not_eq_true] at hHdCond
          simp only [hHdCond] at hHdReduce
          exact ih hHdReduce tid hMemTl tcb hObjTid

/-- WS-SM SM5.I (PR-B capstone): the budget-aware analogue of
`chooseThreadOnCore_selects_highest`.  The thread the *effective* (CBS-budget-
aware) selector dispatches is not `isBetterCandidate`-beaten — on **effective**
`resolveEffectivePrioDeadline` priority/deadline — by any domain-matching,
budget-sufficient thread in core `c`'s maximum-priority bucket (where the
selection genuinely competes).  Non-vacuous in the bucket-success path; vacuous
in the full-scan fallback.  Assembles `chooseBestRunnableEffective_result_fields`
(result = effective params of the selected TCB) with
`chooseBestRunnableEffective_optimal` (no eligible+budget thread beats it). -/
theorem chooseThreadEffectiveOnCore_selects_highest
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (selTcb : TCB)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c)
    (hSel : chooseThreadEffectiveOnCore st c = .ok (some tid))
    (hSelTcb : st.getTcb? tid = some selTcb) :
    ∀ t ∈ (st.scheduler.runQueueOnCore c).maxPriorityBucket, ∀ tcb : TCB,
      st.getTcb? t = some tcb →
      tcb.domain = st.scheduler.activeDomainOnCore c →
      hasSufficientBudget st tcb = true →
        isBetterCandidate
          (resolveEffectivePrioDeadline st selTcb).1 (resolveEffectivePrioDeadline st selTcb).2
          (resolveEffectivePrioDeadline st tcb).1 (resolveEffectivePrioDeadline st tcb).2 = false := by
  intro t ht tcb htTcb htDom hBudget
  obtain ⟨resPrio, resDl, hbucket⟩ := chooseThreadEffectiveOnCore_eq_some_imp_bucket_some st c tid hSel
  have hSelObj : st.objects.get? tid.toObjId = some (.tcb selTcb) :=
    (SystemState.getTcb?_eq_some_iff st tid selTcb).mp hSelTcb
  have hTObj : st.objects.get? t.toObjId = some (.tcb tcb) :=
    (SystemState.getTcb?_eq_some_iff st t tcb).mp htTcb
  have hMaxAll : ∀ u ∈ (st.scheduler.runQueueOnCore c).maxPriorityBucket,
      ∃ utcb : TCB, st.objects.get? u.toObjId = some (.tcb utcb) := by
    intro u hu
    exact runnableThreadsAreTCBs_objects_get? st c hRunnable u
      (RunQueue.membership_implies_flat _ u
        (RunQueue.maxPriorityBucket_subset _ hwf u hu))
  have hElig : (fun tc : TCB => tc.domain == st.scheduler.activeDomainOnCore c) tcb = true := by
    simp [htDom]
  rw [bucketFirstEffective_fullScan_equivalence] at hbucket
  cases hMax : chooseBestRunnableInDomainEffective st
      (st.scheduler.runQueueOnCore c).maxPriorityBucket
      (st.scheduler.activeDomainOnCore c) none with
  | error e => rw [hMax] at hbucket; simp at hbucket
  | ok val =>
    cases val with
    | some r =>
      rw [hMax] at hbucket
      simp only [Except.ok.injEq, Option.some.injEq] at hbucket
      rw [hbucket] at hMax
      obtain ⟨resTcb, hResTcb, hResP, hResD⟩ :=
        chooseBestRunnableEffective_result_fields st
          (fun tc => tc.domain == st.scheduler.activeDomainOnCore c)
          (st.scheduler.runQueueOnCore c).maxPriorityBucket none tid resPrio resDl hMax
          (by intro _ _ _ h; simp at h)
      rw [hSelObj] at hResTcb; cases hResTcb
      have hOpt := chooseBestRunnableEffective_optimal st
        (fun tc => tc.domain == st.scheduler.activeDomainOnCore c)
        (st.scheduler.runQueueOnCore c).maxPriorityBucket tid resPrio resDl hMax hMaxAll
      have hNoBeat := hOpt t ht tcb hTObj hElig hBudget
      rw [hResP, hResD]
      exact hNoBeat
    | none =>
      rw [hMax] at hbucket
      have hNoElig := chooseBestRunnableEffective_none_no_eligible st
        (fun tc => tc.domain == st.scheduler.activeDomainOnCore c)
        (st.scheduler.runQueueOnCore c).maxPriorityBucket hMax t ht tcb hTObj
      simp [htDom, hBudget] at hNoElig

/-- SM5.A budget helper: a `.ok none` from the bucket-first effective selector
forces the full-list fallback scan to also be `.ok none`. -/
theorem chooseBestInBucketEffective_none_imp_toList_none
    (st : SystemState) (rq : RunQueue) (ad : SeLe4n.DomainId)
    (h : chooseBestInBucketEffective st rq ad = .ok none) :
    chooseBestRunnableInDomainEffective st rq.toList ad none = .ok none := by
  rw [bucketFirstEffective_fullScan_equivalence] at h
  cases hMax : chooseBestRunnableInDomainEffective st rq.maxPriorityBucket ad none with
  | error e => rw [hMax] at h; simp at h
  | ok val =>
    cases val with
    | some r => rw [hMax] at h; simp at h
    | none => rw [hMax] at h; simpa using h

/-- SM5.A budget helper: `chooseThreadEffectiveOnCore = .ok none` forces the
underlying bucket-first effective scan to be `.ok none`. -/
theorem chooseThreadEffectiveOnCore_eq_none_imp_bucket_none
    (st : SystemState) (c : CoreId) (h : chooseThreadEffectiveOnCore st c = .ok none) :
    chooseBestInBucketEffective st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok none := by
  unfold chooseThreadEffectiveOnCore at h
  cases hB : chooseBestInBucketEffective st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) with
  | error e => rw [hB] at h; simp at h
  | ok val =>
    cases val with
    | none => rfl
    | some triple => obtain ⟨tid, p, d⟩ := triple; rw [hB] at h; simp at h

/-- WS-SM SM5.A.4 (budget variant, completeness): `chooseThreadEffectiveOnCore`
returns the idle-fallback signal `.ok none` **only** when no thread in core
`c`'s run queue is both in its active domain and has sufficient CBS budget —
so the budget-aware idle fallback never drops a runnable, in-budget thread. -/
theorem chooseThreadEffectiveOnCore_none_no_eligible
    (st : SystemState) (c : CoreId)
    (h : chooseThreadEffectiveOnCore st c = .ok none) :
    ∀ tid ∈ (st.scheduler.runQueueOnCore c).toList, ∀ tcb : TCB,
      st.getTcb? tid = some tcb →
      ¬(tcb.domain = st.scheduler.activeDomainOnCore c ∧ hasSufficientBudget st tcb = true) := by
  intro tid hmem tcb htcb ⟨hDom, hBudget⟩
  have hbucket := chooseThreadEffectiveOnCore_eq_none_imp_bucket_none st c h
  have htoList := chooseBestInBucketEffective_none_imp_toList_none st
    (st.scheduler.runQueueOnCore c) (st.scheduler.activeDomainOnCore c) hbucket
  have hObjGet : st.objects.get? tid.toObjId = some (.tcb tcb) :=
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp htcb
  have hElig := chooseBestRunnableEffective_none_no_eligible st
    (fun t => t.domain == st.scheduler.activeDomainOnCore c)
    (st.scheduler.runQueueOnCore c).toList htoList tid hmem tcb hObjGet
  simp [hDom, hBudget] at hElig

-- ── PR #880 round 7: the budget-aware domain-respect trio (moved from
-- `Operations/PerCoreDomain.lean`, its original SM5.G.4 home, so consumers
-- upstream of the domain module — the `handleRescheduleSgiOnCore` domain
-- wrapper in the timer-tick module — can cite the selection-filter fact) ──

/-- SM5.G.4 helper (budget variant): a `none`-seeded budget-aware fold that selects
`rt` records a thread whose TCB is in domain `ad`.  Like
`chooseBestRunnableEffective_result_props` but extracts **only** the domain
eligibility (the first conjunct of the `eligible && hasSufficientBudget` filter), so
it needs no well-formedness hypothesis (the budget / membership facts are dropped). -/
theorem chooseBestRunnableEffective_result_eligible
    (st : SystemState) (eligible : TCB → Bool) (list : List SeLe4n.ThreadId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (h : chooseBestRunnableEffective st eligible list none = .ok (some (rt, rp, rd))) :
    ∃ rtcb : TCB, st.objects.get? rt.toObjId = some (.tcb rtcb) ∧ eligible rtcb = true := by
  obtain ⟨_, rtcb, hObj, hElig, _⟩ := chooseBestRunnableEffective_result_props st eligible list rt rp rd h
  exact ⟨rtcb, hObj, hElig⟩

/-- SM5.G.4 helper (budget variant): a bucket-first budget-aware selection over the
active domain `ad` records a thread whose TCB is in domain `ad`.  Needs **no**
well-formedness hypothesis — the domain eligibility holds regardless of bucket
structure (only the membership lift needs `wellFormed`). -/
theorem chooseBestInBucketEffective_result_eligible
    (st : SystemState) (rq : RunQueue) (ad : SeLe4n.DomainId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (h : chooseBestInBucketEffective st rq ad = .ok (some (rt, rp, rd))) :
    ∃ rtcb : TCB, st.objects.get? rt.toObjId = some (.tcb rtcb) ∧ rtcb.domain = ad := by
  rw [bucketFirstEffective_fullScan_equivalence] at h
  cases hMax : chooseBestRunnableInDomainEffective st rq.maxPriorityBucket ad none with
  | error e => rw [hMax] at h; simp at h
  | ok val =>
    cases val with
    | some r =>
      rw [hMax] at h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      obtain ⟨rtcb, hObj, hElig⟩ := chooseBestRunnableEffective_result_eligible st
        (fun tc => tc.domain == ad) rq.maxPriorityBucket rt rp rd hMax
      exact ⟨rtcb, hObj, eq_of_beq hElig⟩
    | none =>
      rw [hMax] at h
      obtain ⟨rtcb, hObj, hElig⟩ := chooseBestRunnableEffective_result_eligible st
        (fun tc => tc.domain == ad) rq.toList rt rp rd h
      exact ⟨rtcb, hObj, eq_of_beq hElig⟩

/-- WS-SM SM5.G.4 (budget-aware companion): a thread the budget-aware
`chooseThreadEffectiveOnCore` selects is in core `c`'s active domain.  Mirrors the
non-budget `chooseThreadOnCore_respects_activeDomain` with **no well-formedness
hypothesis** — domain-respect is a property of the selection filter, independent of
run-queue well-formedness (the audit-pass closes the prior `hwf` asymmetry). -/
theorem chooseThreadEffectiveOnCore_respects_activeDomain
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hSel : chooseThreadEffectiveOnCore st c = .ok (some tid))
    (hTcb : st.getTcb? tid = some tcb) :
    tcb.domain = st.scheduler.activeDomainOnCore c := by
  obtain ⟨p, d, hbucket⟩ := chooseThreadEffectiveOnCore_eq_some_imp_bucket_some st c tid hSel
  obtain ⟨rtcb, hObj, hDom⟩ := chooseBestInBucketEffective_result_eligible st
    (st.scheduler.runQueueOnCore c) (st.scheduler.activeDomainOnCore c) tid p d hbucket
  have hObjTcb : st.objects.get? tid.toObjId = some (.tcb tcb) :=
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  rw [hObj] at hObjTcb
  simp only [Option.some.injEq, KernelObject.tcb.injEq] at hObjTcb
  subst hObjTcb
  exact hDom

end SeLe4n.Kernel
