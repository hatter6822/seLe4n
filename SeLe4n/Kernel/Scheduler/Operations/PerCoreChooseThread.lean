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

/-!
# WS-SM SM5.A — Per-core `chooseThread` (lock-set, independence, completeness)

This module is the SM5.A deliverable of the WS-SM Phase 5 per-core
scheduler (plan `docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.1, §5).
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

* **SM5.A.2** `RunQueueLockId` + `chooseThreadOnCoreLockSet` — the per-core
  run-queue lock identifier and the read-only lock-set footprint of
  `chooseThreadOnCore c`, with structural witnesses.
* **SM5.A.3** `chooseThreadOnCore_frame` + the per-core-independence
  corollaries (Theorem 3.1.2) — the selection on core `c` reads only core
  `c`'s run-queue and active-domain slots, so writes to any other core's
  scheduler slots (or to *any* core's `current`) leave it unchanged.
* **SM5.A.4** idle-fallback completeness — `chooseThreadOnCore` never
  errors on a well-formed state (`chooseThreadOnCore_ok_of_runnableTCBs`),
  returns `none` only when no in-domain runnable thread exists
  (`chooseThreadOnCore_none_no_eligible`), and conversely returns `some`
  whenever an in-domain runnable thread is present
  (`chooseThreadOnCore_some_of_eligible`).  The last is the foundation
  SM5.E discharges with the per-core idle thread to obtain the stronger
  `chooseThreadOnCore_always_succeeds`.
* **SM5.A.6** `chooseThreadOnCore_some_mem_runQueueOnCore` — selection
  soundness: a chosen thread is a genuine member of the core's run queue;
  plus the literal preservation form for the `Kernel`-monad `chooseThread`.
* **SM5.A.7** decidability witnesses for the selection result.

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId allCores)

-- ============================================================================
-- §1  SM5.A.2 — Per-core run-queue lock identifier + chooseThread lock-set
-- ============================================================================

/-- WS-SM SM5.A.2: per-core run-queue lock identifier (plan §3.1 / §3.2's
`LockId.runQueue c`).

The per-core run queue is a `SchedulerState` field (`Vector RunQueue
numCores`), **not** a kernel object, so it is *not* addressed by the SM0.I
object-lock `LockId` hierarchy (which keys on `(LockKind, ObjId)`).  A
run-queue lock is identified purely by its `CoreId`.  Keeping it a distinct
typed identifier — rather than overloading the carefully-pinned 10-level
SM0.I `LockKind` hierarchy (`level_strictMono` / `level_surjective` /
`level_bounded`) with an eleventh "runQueue" kind — both preserves that
pinning and faithfully matches the data model: run queues are per-core,
indexed by `CoreId`, never by `ObjId`. -/
structure RunQueueLockId where
  /-- The core whose run-queue slot this lock guards. -/
  core : CoreId
  deriving DecidableEq, Repr

/-- WS-SM SM5.A.2: the lock-set footprint of `chooseThreadOnCore c`
(plan §3.1 / the SM5.A.2 row of §5).

`chooseThreadOnCore c` is a pure read of core `c`'s run-queue slot (and its
active-domain slot, guarded by the same per-core scheduler lock), so it
acquires a single **read** lock on core `c`'s run queue:
`{(RunQueueLockId.mk c, .read)}`.

It reuses SM3.B's `AccessMode` (read / write) so the per-core scheduler
lock declarations speak the same vocabulary as the SM3 object-lock
subsystem — the eventual SM3.C.9 `withLockSet` integration (deferred to
SM5) composes the two.  The declared footprint is exactly the read
footprint of `chooseThreadOnCore` (witnessed by
`chooseThreadOnCore_independent_of_write_off_lockSet` below: a write to any
core *not* in the lock-set leaves the selection unchanged). -/
def chooseThreadOnCoreLockSet (c : CoreId) :
    List (RunQueueLockId × Concurrency.AccessMode) :=
  [(⟨c⟩, .read)]

/-- SM5.A.2: the `chooseThreadOnCore` lock-set is a singleton. -/
@[simp] theorem chooseThreadOnCoreLockSet_length (c : CoreId) :
    (chooseThreadOnCoreLockSet c).length = 1 := rfl

/-- SM5.A.2: every lock in the `chooseThreadOnCore` lock-set is acquired in
**read** mode — the selection is a pure read. -/
theorem chooseThreadOnCoreLockSet_read_only (c : CoreId) :
    ∀ p ∈ chooseThreadOnCoreLockSet c, p.2 = Concurrency.AccessMode.read := by
  intro p hp
  simp only [chooseThreadOnCoreLockSet, List.mem_singleton] at hp
  subst hp; rfl

/-- SM5.A.2: the only lock in the `chooseThreadOnCore c` lock-set is the
run-queue lock for core `c` itself. -/
theorem chooseThreadOnCoreLockSet_core (c : CoreId) :
    ∀ p ∈ chooseThreadOnCoreLockSet c, p.1.core = c := by
  intro p hp
  simp only [chooseThreadOnCoreLockSet, List.mem_singleton] at hp
  subst hp; rfl

/-- SM5.A.2: the lock-set's projected keys are duplicate-free (it is a
singleton), mirroring the SM3.B `LockSet.hUniqueKeys` key-uniqueness
invariant. -/
theorem chooseThreadOnCoreLockSet_keys_nodup (c : CoreId) :
    ((chooseThreadOnCoreLockSet c).map (·.1)).Nodup := by
  simp [chooseThreadOnCoreLockSet]

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
  rw [hObj, hRQ, hAD]

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

/-- WS-SM SM5.A.3 / SM5.A.2 bridge: the lock-set is the exact read
footprint.  A run-queue write on a core *not* listed in
`chooseThreadOnCoreLockSet c` (equivalently, any `c' ≠ c`) leaves the
selection unchanged.  This connects the SM5.A.2 lock-set declaration to the
SM5.A.3 independence result: the declared lock-set cores are precisely the
cores the selection depends on. -/
theorem chooseThreadOnCore_independent_of_write_off_lockSet
    (s : SystemState) (c c' : CoreId) (rq : RunQueue)
    (h : c' ∉ (chooseThreadOnCoreLockSet c).map (·.1.core)) :
    chooseThreadOnCore
        { s with scheduler := s.scheduler.setRunQueueOnCore c' rq } c
      = chooseThreadOnCore s c := by
  have hne : c ≠ c' := by
    intro heq
    apply h
    simp [chooseThreadOnCoreLockSet, heq]
  exact chooseThreadOnCore_independent_of_setRunQueueOnCore s c c' rq hne

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
    | none => rw [hObj] at h; simp at h
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
      | schedContext _ => rw [hObj] at h; simp at h

/-- SM5.A.4 helper: a fold starting from `none` that returns `.ok none`
witnesses that **every** scanned TCB was ineligible.  (A non-TCB entry
would have produced `.error`, and an eligible TCB would have produced
`.ok (some _)` by `_some_ne_ok_none`.) -/
private theorem chooseBestRunnableBy_none_no_eligible
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
      | none => rw [hHdObj] at hHdReduce; simp at hHdReduce
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
        | schedContext _ => rw [hHdObj] at hHdReduce; simp at hHdReduce

/-- SM5.A.4 helper: a fold over a list whose every entry resolves to a TCB
never errors — it returns `.ok _`.  This is the "no `schedulerInvariant`
violation under a well-formed run queue" property the idle-fallback
completeness rests on. -/
private theorem chooseBestRunnableBy_ok_of_allTcb
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
    | none => rw [hObj] at h; simp at h
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
      | schedContext _ => rw [hObj] at h; simp at h

/-- SM5.A.4 / SM5.A.6 helper: selection soundness for a `none`-seeded
fold — a recorded candidate is a member of the scanned list. -/
private theorem chooseBestRunnableBy_result_mem
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
private theorem chooseBestInBucket_none_imp_toList_none
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
private theorem chooseBestInBucket_ok_of_allTcb
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
private theorem chooseBestInBucket_result_mem
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
private theorem chooseThreadOnCore_eq_none_imp_bucket_none
    (st : SystemState) (c : CoreId) (h : chooseThreadOnCore st c = .ok none) :
    chooseBestInBucket st.objects.get? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok none := by
  unfold chooseThreadOnCore at h
  cases hB : chooseBestInBucket st.objects.get? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) with
  | error e => rw [hB] at h; simp at h
  | ok val =>
    cases val with
    | none => rfl
    | some triple => obtain ⟨tid, p, d⟩ := triple; rw [hB] at h; simp at h

/-- SM5.A.6 helper: `chooseThreadOnCore = .ok (some tid)` exposes the
selected `(tid, priority, deadline)` triple from the bucket-first scan. -/
private theorem chooseThreadOnCore_eq_some_imp_bucket_some
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (h : chooseThreadOnCore st c = .ok (some tid)) :
    ∃ p d, chooseBestInBucket st.objects.get? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok (some (tid, p, d)) := by
  unfold chooseThreadOnCore at h
  cases hB : chooseBestInBucket st.objects.get? (st.scheduler.runQueueOnCore c)
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
private theorem chooseThreadOnCore_ok_of_bucket_ok
    (st : SystemState) (c : CoreId)
    (val : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (h : chooseBestInBucket st.objects.get? (st.scheduler.runQueueOnCore c)
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

-- ============================================================================
-- §4  SM5.A.7 — Decidability of the selection result
-- ============================================================================

/-- WS-SM SM5.A.7: "core `c` selects `tid`" — the decidable proposition the
SM5.A unit tests discharge on concrete states by `decide`.  Decidability
flows from `DecidableEq (Except KernelError (Option ThreadId))` (both
`KernelError` and `ThreadId` derive `DecidableEq`). -/
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

end SeLe4n.Kernel
