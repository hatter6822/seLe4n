-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Core
import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick

/-!
# WS-SM SM5.G — Per-core domain scheduling

Per-core domain scheduling (plan `docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md`
§3.7, §5): each core independently rotates its **own** domain schedule, so
different cores can be in different scheduling domains simultaneously — maximising
parallelism while still bounding per-domain CPU share (plan §4.2).

This module collects the SM5.G theorem surface on top of the SM4.B per-core
`SchedulerState` domain fields (`activeDomainOnCore`, `domainScheduleIndexOnCore`,
`domainTimeRemainingOnCore`) and the SM5.A selector `chooseThreadOnCore`.

* **SM5.G.1** — the per-core active-domain query is the existing
  `SchedulerState.activeDomainOnCore` accessor (the form plan §3.7's
  `s.scheduler.activeDomainOnCore c` uses); it is recapped here by the
  rotation-query lemmas `advanceDomainOnCore_rotates` / `_activeDomainOnCore_ne`.
* **SM5.G.2** — `advanceDomainOnCore`, the *pure* per-core domain rotation, plus
  its frame lemmas, the single-step index/domain/time formulas, the bridge to the
  operational `switchDomainOnCore` (the production domain switch's domain effect
  *is* this rotation), and the **cyclic theorem** (`advanceDomainOnCore_cyclic` —
  iterating `advanceDomainOnCore` `domainSchedule.length` times returns the
  schedule index to its start).
* **SM5.G.3** — `advanceDomainOnCore` *establishes* the SM4.C predicate
  `activeDomainOnCore_isInDomainSchedule` (unconditionally) and *preserves* it on
  the untouched cores; the literal plan §3.7 Theorem 3.7.1 membership form
  (`activeDomainOnCore_isInDomainSchedule_mem`) follows.
* **SM5.G.4** — `chooseThreadOnCore_respects_activeDomain`: every thread selected
  by `chooseThreadOnCore` is in core `c`'s active domain (and its budget-aware
  companion).
* **SM5.G.5** — cross-core domain independence: `advanceDomainOnCore st c` frames
  every other core's scheduler reads, so `chooseThreadOnCore · c'` is unchanged for
  `c' ≠ c`; the `advanceDomainOnCoreLockSet` footprint structurally pins the
  rotation to core `c`'s (per-core scheduler) run-queue lock.

All theorems are proved with no dependency beyond Lean's foundational `propext` /
`Quot.sound` / `Classical.choice`.  `advanceDomainOnCore` is forward-looking
infrastructure (the
live tick path rotates via `scheduleDomainOnCore` → `switchDomainOnCore`), so this
module is staged via `Platform.Staged`; the SM5.I per-core run loop is the first
runtime exerciser.
-/

/-- WS-SM SM5.G.1 (plan §3.7): the per-core active scheduling domain, queried at the
`SystemState` level.  This is the literal §3.7 accessor `activeDomainOnCore
(s : SystemState) (c : CoreId) : DomainId`, a thin wrapper over the SM4.B
`SchedulerState.activeDomainOnCore`.  It is made load-bearing by the §3.7 Theorem
3.7.1 membership form `SystemState.activeDomainOnCore_mem` (below); the deeper SM5.G
theorems are stated over `s.scheduler.activeDomainOnCore c` (the form the SM4.B
store/load `@[simp]` algebra targets), and the `@[simp]` bridge
`SystemState.activeDomainOnCore_eq` reduces this wrapper to that form so every
existing lemma keeps firing. -/
def SeLe4n.Model.SystemState.activeDomainOnCore (s : SeLe4n.Model.SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) : SeLe4n.DomainId :=
  s.scheduler.activeDomainOnCore c

@[simp] theorem SeLe4n.Model.SystemState.activeDomainOnCore_eq (s : SeLe4n.Model.SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    s.activeDomainOnCore c = s.scheduler.activeDomainOnCore c := rfl

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId)

-- ============================================================================
-- §1  SM5.G.2 — `advanceDomainOnCore`: pure per-core domain rotation
-- ============================================================================

/-- WS-SM SM5.G.2 (plan §3.7): pure per-core domain rotation.

`advanceDomainOnCore st c` rotates **core `c`'s** domain-schedule state by one
step: it advances core `c`'s `domainScheduleIndexOnCore` to `(idx + 1) mod
length`, sets its `activeDomainOnCore` to the next schedule entry's domain, and
resets its `domainTimeRemainingOnCore` to that entry's length.  It writes **only**
core `c`'s domain triple — never the run queue, the current thread, the object
store, or any other core's slots.

This is the *abstract* domain rotation primitive: unlike the operational
`switchDomainOnCore` (SM5.D.6) it does **not** save the outgoing register context,
re-enqueue the current thread, or clear `currentOnCore`.  It is the pure
domain-state effect that the cyclic theorem (`advanceDomainOnCore_cyclic`) and the
domain-membership theorem (`advanceDomainOnCore_establishes_…`) reason about; the
bridge `switchDomainOnCore_domainTriple_eq_advanceDomainOnCore` proves the
operational switch's *entire* domain-state effect (active domain + time remaining +
schedule index) is exactly this rotation.

Single-domain mode is a no-op: when `domainSchedule = []`, the lookup index `(idx +
1) % 0 = idx + 1` is out of bounds of the empty list, so `domainSchedule[…]? = none`
and the rotation returns `st` unchanged (the `none` arm) — exactly mirroring
`switchDomainOnCore`'s `[] => .ok st`.  The single `Option`-lookup match subsumes
the empty-schedule case, so no separate `| [] =>` arm is needed. -/
def advanceDomainOnCore (st : SystemState) (c : CoreId) : SystemState :=
  match st.scheduler.domainSchedule[((st.scheduler.domainScheduleIndexOnCore c) + 1) %
      st.scheduler.domainSchedule.length]? with
  | none => st
  | some entry =>
      { st with scheduler :=
          (((st.scheduler.setActiveDomainOnCore c (DomainScheduleEntry.domain entry)).setDomainTimeRemainingOnCore
            c (DomainScheduleEntry.length entry)).setDomainScheduleIndexOnCore c
            (((st.scheduler.domainScheduleIndexOnCore c) + 1) % st.scheduler.domainSchedule.length)) }

/-- WS-SM SM5.G.2: single-domain mode is a no-op (no rotation when the schedule is
empty), mirroring `switchDomainOnCore_singleDomain_noop`. -/
theorem advanceDomainOnCore_empty (st : SystemState) (c : CoreId)
    (h : st.scheduler.domainSchedule = []) :
    advanceDomainOnCore st c = st := by
  unfold advanceDomainOnCore; simp [h]

-- ── Frame lemmas: the rotation touches only core `c`'s domain triple. ──

/-- WS-SM SM5.G.2/.5: the rotation never touches the object store. -/
@[simp] theorem advanceDomainOnCore_objects (st : SystemState) (c : CoreId) :
    (advanceDomainOnCore st c).objects = st.objects := by
  unfold advanceDomainOnCore; split <;> rfl

/-- WS-SM SM5.G.4/.5: the rotation frames every thread's TCB resolution (it does
not touch the object store). -/
theorem advanceDomainOnCore_getTcb? (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    (advanceDomainOnCore st c).getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?; rw [advanceDomainOnCore_objects]

/-- WS-SM SM5.G.2: the (system-wide) domain schedule is unchanged — the rotation
advances the per-core *index*, never rewrites the schedule table.  Needed for the
cyclic iteration (the schedule length is invariant across rotations). -/
@[simp] theorem advanceDomainOnCore_domainSchedule (st : SystemState) (c : CoreId) :
    (advanceDomainOnCore st c).scheduler.domainSchedule = st.scheduler.domainSchedule := by
  unfold advanceDomainOnCore
  split
  · rfl
  · simp [SchedulerState.setActiveDomainOnCore, SchedulerState.setDomainTimeRemainingOnCore,
      SchedulerState.setDomainScheduleIndexOnCore]

/-- WS-SM SM5.G.5: the rotation frames every core's run queue (it never touches a
run queue at all). -/
@[simp] theorem advanceDomainOnCore_runQueueOnCore (st : SystemState) (c c' : CoreId) :
    (advanceDomainOnCore st c).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold advanceDomainOnCore; split <;> simp

/-- WS-SM SM5.G.5: the rotation frames every core's current thread (it never
touches a `current` slot). -/
@[simp] theorem advanceDomainOnCore_currentOnCore (st : SystemState) (c c' : CoreId) :
    (advanceDomainOnCore st c).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  unfold advanceDomainOnCore; split <;> simp

/-- WS-SM SM5.G.5: the rotation frames every other core's active domain. -/
@[simp] theorem advanceDomainOnCore_activeDomainOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (advanceDomainOnCore st c).scheduler.activeDomainOnCore c' = st.scheduler.activeDomainOnCore c' := by
  unfold advanceDomainOnCore; split <;> simp [h]

/-- WS-SM SM5.G.5: the rotation frames every other core's domain time remaining. -/
@[simp] theorem advanceDomainOnCore_domainTimeRemainingOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (advanceDomainOnCore st c).scheduler.domainTimeRemainingOnCore c' = st.scheduler.domainTimeRemainingOnCore c' := by
  unfold advanceDomainOnCore; split <;> simp [h]

/-- WS-SM SM5.G.5: the rotation frames every other core's domain-schedule index. -/
@[simp] theorem advanceDomainOnCore_domainScheduleIndexOnCore_ne (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (advanceDomainOnCore st c).scheduler.domainScheduleIndexOnCore c' = st.scheduler.domainScheduleIndexOnCore c' := by
  unfold advanceDomainOnCore; split <;> simp [h]

-- ── Single-step rotation formulas (the `some entry` branch, non-empty). ──

/-- WS-SM SM5.G.1/.2 (the active-domain query after a rotation): when the schedule
lookup at the next index yields `entry`, the rotated active domain on core `c` is
`entry`'s domain.  This is `switchDomainOnCore_rotates`'s pure-rotation analogue.
A successful `some entry` lookup already implies the schedule is non-empty, so no
separate non-empty hypothesis is needed. -/
theorem advanceDomainOnCore_rotates (st : SystemState) (c : CoreId)
    (entry : DomainScheduleEntry)
    (hLookup : st.scheduler.domainSchedule[((st.scheduler.domainScheduleIndexOnCore c) + 1) %
        st.scheduler.domainSchedule.length]? = some entry) :
    (advanceDomainOnCore st c).scheduler.activeDomainOnCore c = DomainScheduleEntry.domain entry := by
  unfold advanceDomainOnCore
  rw [hLookup]
  simp [SchedulerState.setDomainScheduleIndexOnCore_activeDomainOnCore,
    SchedulerState.setDomainTimeRemainingOnCore_activeDomainOnCore,
    SchedulerState.setActiveDomainOnCore_activeDomainOnCore_self]

/-- WS-SM SM5.G.2: the rotation resets core `c`'s domain time remaining to the next
entry's length (the per-domain quantum). -/
theorem advanceDomainOnCore_domainTimeRemainingOnCore_self (st : SystemState) (c : CoreId)
    (entry : DomainScheduleEntry)
    (hLookup : st.scheduler.domainSchedule[((st.scheduler.domainScheduleIndexOnCore c) + 1) %
        st.scheduler.domainSchedule.length]? = some entry) :
    (advanceDomainOnCore st c).scheduler.domainTimeRemainingOnCore c = DomainScheduleEntry.length entry := by
  unfold advanceDomainOnCore
  rw [hLookup]
  simp [SchedulerState.setDomainScheduleIndexOnCore_domainTimeRemainingOnCore,
    SchedulerState.setDomainTimeRemainingOnCore_domainTimeRemainingOnCore_self]

/-- WS-SM SM5.G.2: the single-step index advance — on a non-empty schedule, the
rotation advances core `c`'s schedule index to `(idx + 1) mod length`. -/
theorem advanceDomainOnCore_domainScheduleIndexOnCore_self (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule ≠ []) :
    (advanceDomainOnCore st c).scheduler.domainScheduleIndexOnCore c
      = ((st.scheduler.domainScheduleIndexOnCore c) + 1) % st.scheduler.domainSchedule.length := by
  unfold advanceDomainOnCore
  have hbound : ((st.scheduler.domainScheduleIndexOnCore c) + 1) % st.scheduler.domainSchedule.length
      < st.scheduler.domainSchedule.length := Nat.mod_lt _ (List.length_pos_iff.mpr hSched)
  rw [List.getElem?_eq_getElem hbound]
  simp

/-- WS-SM SM5.G.2: the rotated index is always a valid (in-bounds) schedule index
on a non-empty schedule.  (The cyclic character: the index always stays in
`[0, length)`.) -/
theorem advanceDomainOnCore_index_lt (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule ≠ []) :
    (advanceDomainOnCore st c).scheduler.domainScheduleIndexOnCore c
      < st.scheduler.domainSchedule.length := by
  rw [advanceDomainOnCore_domainScheduleIndexOnCore_self st c hSched]
  exact Nat.mod_lt _ (List.length_pos_iff.mpr hSched)

-- ============================================================================
-- §2  SM5.G.2 — cyclic theorem (`advanceDomainOnCore_cyclic`)
-- ============================================================================

/-- WS-SM SM5.G.2: `k`-fold per-core domain rotation — apply `advanceDomainOnCore
· c` to `st` exactly `k` times.  The recursive helper the cyclic theorem iterates
over (the core-only toolchain has no `Function.iterate`). -/
def advanceDomainOnCoreN (st : SystemState) (c : CoreId) : Nat → SystemState
  | 0 => st
  | k + 1 => advanceDomainOnCore (advanceDomainOnCoreN st c k) c

@[simp] theorem advanceDomainOnCoreN_zero (st : SystemState) (c : CoreId) :
    advanceDomainOnCoreN st c 0 = st := rfl

theorem advanceDomainOnCoreN_succ (st : SystemState) (c : CoreId) (k : Nat) :
    advanceDomainOnCoreN st c (k + 1) = advanceDomainOnCore (advanceDomainOnCoreN st c k) c := rfl

/-- WS-SM SM5.G.2: the (system-wide) schedule table is invariant under any number
of rotations (each rotation advances only the per-core index). -/
@[simp] theorem advanceDomainOnCoreN_domainSchedule (st : SystemState) (c : CoreId) (k : Nat) :
    (advanceDomainOnCoreN st c k).scheduler.domainSchedule = st.scheduler.domainSchedule := by
  induction k with
  | zero => rfl
  | succ k ih => rw [advanceDomainOnCoreN_succ, advanceDomainOnCore_domainSchedule, ih]

/-- File-local arithmetic helper: `(a mod L + 1) mod L = (a + 1) mod L` (the
inductive step's index normalisation, valid for every `L` including `0`). -/
private theorem mod_add_one_mod (a L : Nat) : (a % L + 1) % L = (a + 1) % L := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd a (Nat.dvd_refl L), ← Nat.add_mod]

/-- WS-SM SM5.G.2 (the schedule-index iteration formula): on a non-empty schedule,
after `k` rotations core `c`'s schedule index is `(idx + k) mod length`.  Requires
the starting index to be in bounds (`idx < length`), which the scheduler invariant
maintains (boot sets it to `0`; every rotation sets it to `… mod length < length`,
witnessed by `advanceDomainOnCore_index_lt`). -/
theorem advanceDomainOnCoreN_index (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hidx : st.scheduler.domainScheduleIndexOnCore c < st.scheduler.domainSchedule.length)
    (k : Nat) :
    (advanceDomainOnCoreN st c k).scheduler.domainScheduleIndexOnCore c
      = ((st.scheduler.domainScheduleIndexOnCore c) + k) % st.scheduler.domainSchedule.length := by
  induction k with
  | zero =>
    simp only [advanceDomainOnCoreN_zero, Nat.add_zero]
    exact (Nat.mod_eq_of_lt hidx).symm
  | succ k ih =>
    rw [advanceDomainOnCoreN_succ]
    have hSched' : (advanceDomainOnCoreN st c k).scheduler.domainSchedule ≠ [] := by
      rw [advanceDomainOnCoreN_domainSchedule]; exact hSched
    rw [advanceDomainOnCore_domainScheduleIndexOnCore_self _ _ hSched',
      advanceDomainOnCoreN_domainSchedule, ih, mod_add_one_mod, Nat.add_assoc]

/-- WS-SM SM5.G.2 (**cyclic theorem**, plan §3.7): iterating the per-core domain
rotation exactly `domainSchedule.length` times returns core `c`'s schedule index to
its starting value — the schedule cycles with period `length`.  This is the
defining property of round-robin domain scheduling: each core walks every entry of
its (shared) schedule table and returns to the start, giving every domain its
quantum in turn.  (Requires `idx < length`, as in `advanceDomainOnCoreN_index`.) -/
theorem advanceDomainOnCore_cyclic (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hidx : st.scheduler.domainScheduleIndexOnCore c < st.scheduler.domainSchedule.length) :
    (advanceDomainOnCoreN st c st.scheduler.domainSchedule.length).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c := by
  rw [advanceDomainOnCoreN_index st c hSched hidx, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hidx

-- ============================================================================
-- §3  SM5.G.2 — bridge: the operational `switchDomainOnCore`'s domain effect
--     *is* `advanceDomainOnCore`'s rotation
-- ============================================================================

/-- WS-SM SM5.G.2 (bridge to production): a successful operational domain switch
(`switchDomainOnCore`, SM5.D.6 — which *also* re-dispatches: saves context,
re-enqueues the current thread, clears `current`) advances core `c`'s active domain
to exactly the value the pure rotation `advanceDomainOnCore` computes.  This wires
the abstract rotation into the live domain-switch path: `advanceDomainOnCore` is
not an orphan — it is the canonical domain-state effect of the production
transition.  (The two transitions differ *only* in their run-queue / current /
register-context effects, never in the domain triple.) -/
theorem switchDomainOnCore_activeDomain_eq_advanceDomainOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (hStep : switchDomainOnCore st c = .ok st') :
    st'.scheduler.activeDomainOnCore c = (advanceDomainOnCore st c).scheduler.activeDomainOnCore c := by
  by_cases hSched : st.scheduler.domainSchedule = []
  · rw [switchDomainOnCore_singleDomain_noop st c hSched] at hStep
    injection hStep with hStep'
    subst hStep'
    rw [advanceDomainOnCore_empty st c hSched]
  · have hlen : 0 < st.scheduler.domainSchedule.length := List.length_pos_iff.mpr hSched
    have hbound : ((st.scheduler.domainScheduleIndexOnCore c) + 1) % st.scheduler.domainSchedule.length
        < st.scheduler.domainSchedule.length := Nat.mod_lt _ hlen
    obtain ⟨entry, hEntry⟩ :
        ∃ e, st.scheduler.domainSchedule[((st.scheduler.domainScheduleIndexOnCore c) + 1) %
          st.scheduler.domainSchedule.length]? = some e := ⟨_, List.getElem?_eq_getElem hbound⟩
    rw [switchDomainOnCore_rotates st c st' entry hEntry hSched hStep,
      advanceDomainOnCore_rotates st c entry hEntry]

-- ============================================================================
-- §4  SM5.G.3 — `activeDomainOnCore_isInDomainSchedule` (plan §3.7, Thm 3.7.1)
-- ============================================================================

/-- WS-SM SM5.G.3: a per-core domain rotation **establishes** the SM4.C predicate
`activeDomainOnCore_isInDomainSchedule` on the rotated core, *unconditionally*
(needs no precondition).  On a non-empty schedule the rotated active domain is the
domain of a genuine schedule entry; on an empty schedule the predicate's
single-domain-mode disjunct holds.  This is the substantive content of SM5.G.3: the
rotation always lands on a domain that is actually in the schedule — it never
fabricates a phantom domain. -/
theorem advanceDomainOnCore_establishes_activeDomainOnCore_isInDomainSchedule
    (st : SystemState) (c : CoreId) :
    activeDomainOnCore_isInDomainSchedule (advanceDomainOnCore st c) c := by
  unfold activeDomainOnCore_isInDomainSchedule
  rw [advanceDomainOnCore_domainSchedule]
  by_cases hSched : st.scheduler.domainSchedule = []
  · exact Or.inl hSched
  · right
    have hbound : ((st.scheduler.domainScheduleIndexOnCore c) + 1) % st.scheduler.domainSchedule.length
        < st.scheduler.domainSchedule.length := Nat.mod_lt _ (List.length_pos_iff.mpr hSched)
    obtain ⟨entry, hEntry⟩ :
        ∃ e, st.scheduler.domainSchedule[((st.scheduler.domainScheduleIndexOnCore c) + 1) %
          st.scheduler.domainSchedule.length]? = some e := ⟨_, List.getElem?_eq_getElem hbound⟩
    exact ⟨entry, List.mem_of_getElem? hEntry,
      (advanceDomainOnCore_rotates st c entry hEntry).symm⟩

/-- WS-SM SM5.G.3 (frame): on a core `c' ≠ c` the rotation does not change the
active domain, so it **preserves** `activeDomainOnCore_isInDomainSchedule` there. -/
theorem advanceDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule_ne
    (st : SystemState) (c c' : CoreId) (h : c ≠ c')
    (hPred : activeDomainOnCore_isInDomainSchedule st c') :
    activeDomainOnCore_isInDomainSchedule (advanceDomainOnCore st c) c' := by
  unfold activeDomainOnCore_isInDomainSchedule at hPred ⊢
  rw [advanceDomainOnCore_domainSchedule, advanceDomainOnCore_activeDomainOnCore_ne st c c' h]
  exact hPred

/-- WS-SM SM5.G.3 (SMP preservation): if **every** core's active domain is in the
schedule, then rotating any single core `c` preserves that — the rotated core
*establishes* it afresh, every other core is framed.  This is the per-core domain
rotation's contribution to the system-wide `schedulerInvariant_smp_crossSubsystem`
that SM5.I maintains. -/
theorem advanceDomainOnCore_preserves_isInDomainSchedule_smp
    (st : SystemState) (c : CoreId)
    (hAll : ∀ c'' : CoreId, activeDomainOnCore_isInDomainSchedule st c'') :
    ∀ c'' : CoreId, activeDomainOnCore_isInDomainSchedule (advanceDomainOnCore st c) c'' := by
  intro c''
  by_cases h : c = c''
  · subst h
    exact advanceDomainOnCore_establishes_activeDomainOnCore_isInDomainSchedule st c
  · exact advanceDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule_ne st c c'' h (hAll c'')

/-- WS-SM SM5.G.3 (plan §3.7, **Theorem 3.7.1** literal form): under the SM4.C
predicate and a non-empty schedule, core `c`'s active domain is a member of the
schedule's domain list.  This is the exact membership statement the plan §3.7
states; it follows from the predicate's (disjunctive) form by ruling out the
empty-schedule disjunct. -/
theorem activeDomainOnCore_isInDomainSchedule_mem (st : SystemState) (c : CoreId)
    (hPred : activeDomainOnCore_isInDomainSchedule st c)
    (hNe : st.scheduler.domainSchedule ≠ []) :
    st.scheduler.activeDomainOnCore c ∈ st.scheduler.domainSchedule.map (·.domain) := by
  rcases hPred with hEmpty | ⟨e, hMem, hEq⟩
  · exact absurd hEmpty hNe
  · rw [← hEq]
    exact List.mem_map_of_mem hMem

/-- WS-SM SM5.G.3: the Theorem 3.7.1 membership discharged from the system-wide SMP
cross-subsystem invariant (`schedulerInvariant_smp_crossSubsystem`, which SM4.C
carries the `activeDomainOnCore_isInDomainSchedule` conjunct of). -/
theorem activeDomainOnCore_isInDomainSchedule_mem_of_smp (st : SystemState) (c : CoreId)
    (hInv : schedulerInvariant_smp_crossSubsystem st)
    (hNe : st.scheduler.domainSchedule ≠ []) :
    st.scheduler.activeDomainOnCore c ∈ st.scheduler.domainSchedule.map (·.domain) :=
  activeDomainOnCore_isInDomainSchedule_mem st c
    (schedulerInvariant_perCore_crossSubsystem_to_activeDomainOnCore_isInDomainSchedule (hInv c)) hNe

/-- WS-SM SM5.G.3: the direct membership form — immediately after a rotation, the
new active domain is in the schedule's domain list (non-empty schedule). -/
theorem advanceDomainOnCore_activeDomain_mem (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule ≠ []) :
    (advanceDomainOnCore st c).scheduler.activeDomainOnCore c
      ∈ (advanceDomainOnCore st c).scheduler.domainSchedule.map (·.domain) :=
  activeDomainOnCore_isInDomainSchedule_mem (advanceDomainOnCore st c) c
    (advanceDomainOnCore_establishes_activeDomainOnCore_isInDomainSchedule st c)
    (by rw [advanceDomainOnCore_domainSchedule]; exact hSched)

-- ============================================================================
-- §5  SM5.G.4 — `chooseThreadOnCore_respects_activeDomain`
-- ============================================================================
--
-- A thread the per-core selector picks is in core `c`'s active domain.  This is
-- the "selection respects the domain barrier" property — the security/correctness
-- guarantee of domain scheduling: a core in domain `d` never dispatches a thread
-- of a different domain (temporal isolation between domains).  The fold-eligibility
-- lemma below mirrors `chooseBestRunnableBy_result_mem` (PerCoreChooseThread.lean):
-- a recorded candidate not only is a member of the scanned list, it also passed the
-- eligibility filter.

/-- SM5.G.4 helper: the result of a `chooseBestRunnableBy` fold (from any `best`
that is itself eligible-witnessed) resolves to a TCB satisfying `eligible`, or was
the recorded `best`.  Mirrors `chooseBestRunnableBy_result_mem_aux` but tracks the
eligibility witness rather than list membership. -/
private theorem chooseBestRunnableBy_result_eligible_aux
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
      (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline),
      chooseBestRunnableBy objects eligible list best = .ok (some (rt, rp, rd)) →
      (∃ rtcb : TCB, objects rt.toObjId = some (.tcb rtcb) ∧ eligible rtcb = true)
        ∨ (∃ p d, best = some (rt, p, d)) := by
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
        by_cases hElig : eligible tcb
        · cases best with
          | none =>
            simp only [hElig, if_true] at h
            rcases ih _ rt rp rd h with hprops | ⟨p, d, hb⟩
            · exact Or.inl hprops
            · simp only [Option.some.injEq, Prod.mk.injEq] at hb
              exact Or.inl ⟨tcb, hb.1 ▸ hObj, hElig⟩
          | some y =>
            obtain ⟨yt, yp, yd⟩ := y
            by_cases hBetter : isBetterCandidate yp yd tcb.priority tcb.deadline
            · simp only [hElig, hBetter, if_true] at h
              rcases ih _ rt rp rd h with hprops | ⟨p, d, hb⟩
              · exact Or.inl hprops
              · simp only [Option.some.injEq, Prod.mk.injEq] at hb
                exact Or.inl ⟨tcb, hb.1 ▸ hObj, hElig⟩
            · simp only [hElig, hBetter, if_true] at h
              rcases ih _ rt rp rd h with hprops | ⟨p, d, hb⟩
              · exact Or.inl hprops
              · exact Or.inr ⟨p, d, hb⟩
        · simp only [hElig] at h
          rcases ih _ rt rp rd h with hprops | hb
          · exact Or.inl hprops
          · exact Or.inr hb
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ => rw [hObj] at h; simp at h

/-- SM5.G.4 helper: a `none`-seeded `chooseBestRunnableBy` fold that selects `rt`
witnesses that `rt` resolves to a TCB satisfying `eligible`. -/
theorem chooseBestRunnableBy_result_eligible
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool)
    (list : List SeLe4n.ThreadId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (h : chooseBestRunnableBy objects eligible list none = .ok (some (rt, rp, rd))) :
    ∃ rtcb : TCB, objects rt.toObjId = some (.tcb rtcb) ∧ eligible rtcb = true := by
  rcases chooseBestRunnableBy_result_eligible_aux objects eligible list none rt rp rd h with
    hp | ⟨_, _, hb⟩
  · exact hp
  · exact absurd hb (by simp)

/-- SM5.G.4 helper: a bucket-first selection (max-bucket scan + full-list fallback)
over the active domain `ad` records a thread whose TCB is in domain `ad`. -/
theorem chooseBestInBucket_result_eligible
    (objects : SeLe4n.ObjId → Option KernelObject) (rq : RunQueue) (ad : SeLe4n.DomainId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (h : chooseBestInBucket objects rq ad = .ok (some (rt, rp, rd))) :
    ∃ rtcb : TCB, objects rt.toObjId = some (.tcb rtcb) ∧ rtcb.domain = ad := by
  rw [bucketFirst_fullScan_equivalence] at h
  cases hMax : chooseBestRunnableInDomain objects rq.maxPriorityBucket ad none with
  | error e => rw [hMax] at h; simp at h
  | ok val =>
    cases val with
    | some r =>
      rw [hMax] at h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      obtain ⟨rtcb, hObj, hElig⟩ := chooseBestRunnableBy_result_eligible objects
        (fun tcb => tcb.domain == ad) rq.maxPriorityBucket rt rp rd hMax
      exact ⟨rtcb, hObj, eq_of_beq hElig⟩
    | none =>
      rw [hMax] at h
      obtain ⟨rtcb, hObj, hElig⟩ := chooseBestRunnableBy_result_eligible objects
        (fun tcb => tcb.domain == ad) rq.toList rt rp rd h
      exact ⟨rtcb, hObj, eq_of_beq hElig⟩

/-- WS-SM SM5.G.4 (plan §3.7, `chooseThreadOnCore_respects_activeDomain`): a thread
selected by `chooseThreadOnCore` on core `c` is in core `c`'s active scheduling
domain.  The domain barrier is honoured by selection: a core never dispatches a
thread of a domain other than its current active one (temporal isolation). -/
theorem chooseThreadOnCore_respects_activeDomain
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hSel : chooseThreadOnCore st c = .ok (some tid))
    (hTcb : st.getTcb? tid = some tcb) :
    tcb.domain = st.scheduler.activeDomainOnCore c := by
  obtain ⟨p, d, hbucket⟩ := chooseThreadOnCore_eq_some_imp_bucket_some st c tid hSel
  obtain ⟨rtcb, hObj, hDom⟩ := chooseBestInBucket_result_eligible st.objects.get?
    (st.scheduler.runQueueOnCore c) (st.scheduler.activeDomainOnCore c) tid p d hbucket
  have hObjTcb : st.objects.get? tid.toObjId = some (.tcb tcb) :=
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  rw [hObj] at hObjTcb
  simp only [Option.some.injEq, KernelObject.tcb.injEq] at hObjTcb
  subst hObjTcb
  exact hDom

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


-- ============================================================================
-- §6  SM5.G.5 — cross-core domain independence + footprint
-- ============================================================================

/-- WS-SM SM5.G.5 (cross-core domain independence): rotating core `c`'s domain
leaves core `c'`'s thread selection unchanged (`c' ≠ c`).  The rotation writes only
core `c`'s domain triple, so the three reads `chooseThreadOnCore` makes on `c'`
(`objects`, `runQueueOnCore c'`, `activeDomainOnCore c'`) are all framed.  Different
cores' domain rotations are independent — the whole point of per-core domain
scheduling (plan §4.2). -/
theorem advanceDomainOnCore_independent_of_other_core (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    chooseThreadOnCore (advanceDomainOnCore st c) c' = chooseThreadOnCore st c' := by
  apply chooseThreadOnCore_frame
  · exact advanceDomainOnCore_objects st c
  · exact advanceDomainOnCore_runQueueOnCore st c c'
  · exact advanceDomainOnCore_activeDomainOnCore_ne st c c' h

/-- WS-SM SM5.G.5 (plan §3.7, the `c₁ ≠ c₂` named form): the selection on core `c₁`
does not depend on core `c₂`'s domain rotation. -/
theorem advanceDomainOnCore_perCore_independence (st : SystemState) (c₁ c₂ : CoreId)
    (h : c₁ ≠ c₂) :
    chooseThreadOnCore (advanceDomainOnCore st c₂) c₁ = chooseThreadOnCore st c₁ :=
  advanceDomainOnCore_independent_of_other_core st c₂ c₁ (Ne.symm h)

/-- WS-SM SM5.G.5: the lock-set footprint of `advanceDomainOnCore c`.

The rotation writes **only** core `c`'s per-core domain triple (`activeDomain` /
`domainTimeRemaining` / `domainScheduleIndex` slots), which are guarded by core
`c`'s per-core scheduler lock — the run-queue lock `SchedLockId.runQueue ⟨c⟩`
(SM5.A.2).  It reads no object store, so its footprint is the single core-`c`
run-queue WRITE lock.  This footprint structurally pins the rotation to core `c`:
disjoint cores have disjoint footprints
(`advanceDomainOnCoreLockSet_disjoint_of_ne`), the structural counterpart of the
`advanceDomainOnCore_independent_of_other_core` semantic frame. -/
def advanceDomainOnCoreLockSet (c : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.runQueue ⟨c⟩, .write) ]

/-- SM5.G.5: the footprint is the single per-core run-queue lock. -/
@[simp] theorem advanceDomainOnCoreLockSet_length (c : CoreId) :
    (advanceDomainOnCoreLockSet c).length = 1 := rfl

/-- SM5.G.5: every lock in the rotation's footprint is acquired in **write** mode
(it mutates core `c`'s domain triple). -/
theorem advanceDomainOnCoreLockSet_write_only (c : CoreId) :
    ∀ p ∈ advanceDomainOnCoreLockSet c, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [advanceDomainOnCoreLockSet, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp; rfl

/-- SM5.G.5: the per-core run-queue write lock is in the rotation's footprint. -/
theorem advanceDomainOnCoreLockSet_contains_runQueue_write (c : CoreId) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ advanceDomainOnCoreLockSet c := by
  simp [advanceDomainOnCoreLockSet]

/-- SM5.G.5: the footprint's projected keys are duplicate-free (trivially, a
singleton). -/
theorem advanceDomainOnCoreLockSet_keys_nodup (c : CoreId) :
    ((advanceDomainOnCoreLockSet c).map (·.1)).Nodup := by
  simp [advanceDomainOnCoreLockSet]

/-- SM5.G.5 (the structural cross-core-independence witness): the run-queue lock of
core `c` is **not** in core `c'`'s rotation footprint (`c ≠ c'`).  Disjoint cores'
domain rotations touch disjoint locks — so they never contend, the lock-discipline
counterpart of `advanceDomainOnCore_independent_of_other_core`. -/
theorem advanceDomainOnCoreLockSet_disjoint_of_ne (c c' : CoreId) (h : c ≠ c') :
    SchedLockId.runQueue (⟨c⟩ : RunQueueLockId)
      ∉ (advanceDomainOnCoreLockSet c').map (·.1) := by
  simp only [advanceDomainOnCoreLockSet, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false]
  intro heq
  injection heq with hrq
  injection hrq with hcore
  exact h hcore

-- ============================================================================
-- §7  SM5.G completion (audit-pass-1)
-- ============================================================================
--
-- Closes the optimality gaps identified in the SM5.G self-audit:
--   * SM5.G.1: the §3.7 `SystemState.activeDomainOnCore` accessor made load-bearing.
--   * SM5.G.2: the bridge to the operational `switchDomainOnCore` extended from the
--     active-domain field alone to the **full domain triple** (index + time + domain).
--   * SM5.G.2: the cyclic theorem's `idx < length` precondition lifted to a maintained
--     invariant (`domainScheduleIndexInBoundsOnCore`) and discharged; the cyclic
--     property extended from the index to the **active domain** (under a domain-
--     consistency invariant).
--   * SM5.G.3: invariant preservation lifted from the abstract rotation to the **live
--     transitions** `switchDomainOnCore` / `scheduleDomainOnCore`.
--   * SM5.G.5: the lock-set footprint given an acquisition-order witness and a
--     write-containment theorem (the rotation writes only core `c`'s per-core
--     scheduler state, which the run-queue lock — the per-core scheduler lock per
--     SM5.A — guards).

-- ── SM5.G.1: the §3.7 Theorem 3.7.1 over the `SystemState.activeDomainOnCore`
--    accessor, making the accessor load-bearing. ──

/-- WS-SM SM5.G.1 (plan §3.7, Theorem 3.7.1 over the SystemState accessor): under the
SM4.C predicate + a non-empty schedule, the `SystemState`-level active-domain query is
a member of the schedule's domain list.  This is the literal §3.7 statement over the
§3.7 accessor; it makes `SystemState.activeDomainOnCore` load-bearing (not an orphan
wrapper). -/
theorem activeDomainOnCore_systemState_mem (st : SystemState) (c : CoreId)
    (hPred : activeDomainOnCore_isInDomainSchedule st c)
    (hNe : st.scheduler.domainSchedule ≠ []) :
    st.activeDomainOnCore c ∈ st.scheduler.domainSchedule.map (·.domain) := by
  rw [SystemState.activeDomainOnCore_eq]
  exact activeDomainOnCore_isInDomainSchedule_mem st c hPred hNe

-- ── SM5.G.2: full domain-triple bridge to the operational `switchDomainOnCore`. ──

/-- WS-SM SM5.G.2 (bridge helper): a successful operational domain switch advances
core `c`'s schedule index to `(idx + 1) mod length` — the same index the pure
rotation computes.  (`switchDomainOnCore_rotates`'s index analogue.) -/
theorem switchDomainOnCore_domainScheduleIndexOnCore_self (st : SystemState) (c : CoreId)
    (st' : SystemState) (hSched : st.scheduler.domainSchedule ≠ [])
    (hStep : switchDomainOnCore st c = .ok st') :
    st'.scheduler.domainScheduleIndexOnCore c
      = ((st.scheduler.domainScheduleIndexOnCore c) + 1) % st.scheduler.domainSchedule.length := by
  unfold switchDomainOnCore at hStep
  cases hcase : st.scheduler.domainSchedule with
  | nil => exact absurd hcase hSched
  | cons hd tl =>
    rw [hcase] at hStep
    dsimp only at hStep
    split at hStep
    · simp at hStep
    · simp only [Except.ok.injEq] at hStep
      subst hStep
      simp [SchedulerState.setDomainScheduleIndexOnCore_domainScheduleIndexOnCore_self]

/-- WS-SM SM5.G.2 (bridge helper): a successful operational domain switch resets core
`c`'s domain time remaining to the next entry's length — the same value the pure
rotation computes.  (`switchDomainOnCore_rotates`'s time analogue.) -/
theorem switchDomainOnCore_domainTimeRemainingOnCore_self (st : SystemState) (c : CoreId)
    (st' : SystemState) (entry : DomainScheduleEntry)
    (hLookup : st.scheduler.domainSchedule[((st.scheduler.domainScheduleIndexOnCore c) + 1) %
        st.scheduler.domainSchedule.length]? = some entry)
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hStep : switchDomainOnCore st c = .ok st') :
    st'.scheduler.domainTimeRemainingOnCore c = DomainScheduleEntry.length entry := by
  unfold switchDomainOnCore at hStep
  cases hcase : st.scheduler.domainSchedule with
  | nil => exact absurd hcase hSched
  | cons hd tl =>
    rw [hcase] at hStep
    dsimp only at hStep
    simp only [hcase] at hLookup
    rw [hLookup] at hStep
    simp only [Except.ok.injEq] at hStep
    subst hStep
    simp [SchedulerState.setDomainScheduleIndexOnCore_domainTimeRemainingOnCore,
      SchedulerState.setDomainTimeRemainingOnCore_domainTimeRemainingOnCore_self]

/-- WS-SM SM5.G.2 (the **full** domain-effect bridge): a successful operational
`switchDomainOnCore` and the pure `advanceDomainOnCore` agree on **all three** domain
fields (active domain, time remaining, schedule index) on core `c`.  This upgrades the
active-domain-only `switchDomainOnCore_activeDomain_eq_advanceDomainOnCore` to the
complete characterisation: the production switch's *entire* domain-state effect IS the
pure rotation. -/
theorem switchDomainOnCore_domainTriple_eq_advanceDomainOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (hStep : switchDomainOnCore st c = .ok st') :
    st'.scheduler.activeDomainOnCore c = (advanceDomainOnCore st c).scheduler.activeDomainOnCore c ∧
    st'.scheduler.domainTimeRemainingOnCore c = (advanceDomainOnCore st c).scheduler.domainTimeRemainingOnCore c ∧
    st'.scheduler.domainScheduleIndexOnCore c = (advanceDomainOnCore st c).scheduler.domainScheduleIndexOnCore c := by
  by_cases hSched : st.scheduler.domainSchedule = []
  · rw [switchDomainOnCore_singleDomain_noop st c hSched] at hStep
    injection hStep with hStep'
    subst hStep'
    rw [advanceDomainOnCore_empty st c hSched]
    exact ⟨rfl, rfl, rfl⟩
  · have hbound : ((st.scheduler.domainScheduleIndexOnCore c) + 1) % st.scheduler.domainSchedule.length
        < st.scheduler.domainSchedule.length := Nat.mod_lt _ (List.length_pos_iff.mpr hSched)
    obtain ⟨entry, hEntry⟩ :
        ∃ e, st.scheduler.domainSchedule[((st.scheduler.domainScheduleIndexOnCore c) + 1) %
          st.scheduler.domainSchedule.length]? = some e := ⟨_, List.getElem?_eq_getElem hbound⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [switchDomainOnCore_rotates st c st' entry hEntry hSched hStep,
        advanceDomainOnCore_rotates st c entry hEntry]
    · rw [switchDomainOnCore_domainTimeRemainingOnCore_self st c st' entry hEntry hSched hStep,
        advanceDomainOnCore_domainTimeRemainingOnCore_self st c entry hEntry]
    · rw [switchDomainOnCore_domainScheduleIndexOnCore_self st c st' hSched hStep,
        advanceDomainOnCore_domainScheduleIndexOnCore_self st c hSched]

-- ── SM5.G.5: lock-set acquisition order + write-containment. ──

/-- WS-SM SM5.G.5: the rotation footprint's projected keys form a valid `withLockSet`
acquisition order (trivially — a singleton).  Mirrors the sibling
`enqueueIdleThreadOnCoreLockSet_pairwise_le`. -/
theorem advanceDomainOnCoreLockSet_pairwise_le (c : CoreId) :
    ((advanceDomainOnCoreLockSet c).map (·.1)).Pairwise (· ≤ ·) := by
  simp only [advanceDomainOnCoreLockSet, List.map_cons, List.map_nil]
  exact List.pairwise_singleton _ _

/-- WS-SM SM5.G.5 (footprint soundness): the rotation's write set is **contained in
core `c`'s per-core scheduler state**.  It leaves the object store untouched and every
*other* core `c'`'s scheduler slots untouched — so the only state it writes is core
`c`'s domain triple, which the run-queue lock `SchedLockId.runQueue ⟨c⟩` guards (the
per-core scheduler lock, per SM5.A's `RunQueueLockId`).  This is the formal content
behind the `advanceDomainOnCoreLockSet` declaration: nothing outside the footprint's
lock scope is modified. -/
theorem advanceDomainOnCore_frames_outside_core (st : SystemState) (c c' : CoreId)
    (h : c ≠ c') :
    (advanceDomainOnCore st c).objects = st.objects ∧
    (advanceDomainOnCore st c).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' ∧
    (advanceDomainOnCore st c).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' ∧
    (advanceDomainOnCore st c).scheduler.activeDomainOnCore c' = st.scheduler.activeDomainOnCore c' ∧
    (advanceDomainOnCore st c).scheduler.domainTimeRemainingOnCore c' = st.scheduler.domainTimeRemainingOnCore c' ∧
    (advanceDomainOnCore st c).scheduler.domainScheduleIndexOnCore c' = st.scheduler.domainScheduleIndexOnCore c' :=
  ⟨advanceDomainOnCore_objects st c,
   advanceDomainOnCore_runQueueOnCore st c c',
   advanceDomainOnCore_currentOnCore st c c',
   advanceDomainOnCore_activeDomainOnCore_ne st c c' h,
   advanceDomainOnCore_domainTimeRemainingOnCore_ne st c c' h,
   advanceDomainOnCore_domainScheduleIndexOnCore_ne st c c' h⟩

-- ============================================================================
-- §8  SM5.G.2 — the index-bounds invariant + the discharged cyclic theorem
-- ============================================================================

/-- WS-SM SM5.G.2 (the schedule-index-bounds invariant): core `c`'s schedule index is
in bounds, or the schedule is empty (single-domain mode).  This is the property the
cyclic theorem's `idx < length` precondition rests on; it is maintained by the domain
transitions (the boot state has an empty schedule; every rotation sets the index to
`… mod length < length`). -/
def domainScheduleIndexInBoundsOnCore (st : SystemState) (c : CoreId) : Prop :=
  st.scheduler.domainSchedule = [] ∨
  st.scheduler.domainScheduleIndexOnCore c < st.scheduler.domainSchedule.length

/-- WS-SM SM5.G.2: the freshly-booted system satisfies the index-bounds invariant
(empty schedule → the single-domain-mode disjunct). -/
theorem default_domainScheduleIndexInBoundsOnCore (c : CoreId) :
    domainScheduleIndexInBoundsOnCore (default : SystemState) c := Or.inl rfl

/-- WS-SM SM5.G.2: a per-core domain rotation **establishes** the index-bounds
invariant on the rotated core, unconditionally (after any rotation the index is
`(idx + 1) mod length < length`, or the schedule is empty and the rotation no-ops). -/
theorem advanceDomainOnCore_establishes_domainScheduleIndexInBoundsOnCore
    (st : SystemState) (c : CoreId) :
    domainScheduleIndexInBoundsOnCore (advanceDomainOnCore st c) c := by
  unfold domainScheduleIndexInBoundsOnCore
  rw [advanceDomainOnCore_domainSchedule]
  by_cases hSched : st.scheduler.domainSchedule = []
  · exact Or.inl hSched
  · exact Or.inr (advanceDomainOnCore_index_lt st c hSched)

/-- WS-SM SM5.G.2 (frame): on a core `c' ≠ c` the rotation does not change the index or
schedule, so it **preserves** the index-bounds invariant there. -/
theorem advanceDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore_ne
    (st : SystemState) (c c' : CoreId) (h : c ≠ c')
    (hInv : domainScheduleIndexInBoundsOnCore st c') :
    domainScheduleIndexInBoundsOnCore (advanceDomainOnCore st c) c' := by
  unfold domainScheduleIndexInBoundsOnCore at hInv ⊢
  rw [advanceDomainOnCore_domainSchedule, advanceDomainOnCore_domainScheduleIndexOnCore_ne st c c' h]
  exact hInv

/-- WS-SM SM5.G.2 (**cyclic theorem, discharged from the invariant**): the index-cyclic
property with the raw `idx < length` precondition replaced by the maintained
`domainScheduleIndexInBoundsOnCore` invariant.  This is the form a caller holding the
invariant (SM5.I) uses directly. -/
theorem advanceDomainOnCore_cyclic_of_inBounds (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hInv : domainScheduleIndexInBoundsOnCore st c) :
    (advanceDomainOnCoreN st c st.scheduler.domainSchedule.length).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c := by
  refine advanceDomainOnCore_cyclic st c hSched ?_
  rcases hInv with hEmpty | hLt
  · exact absurd hEmpty hSched
  · exact hLt

-- ============================================================================
-- §9  SM5.G.2 — the domain-consistency invariant + the active-domain cyclic
-- ============================================================================

/-- WS-SM SM5.G.2 (the domain-consistency invariant): core `c`'s active domain matches
the domain of the schedule entry at its current index.  Vacuously true when the
schedule is empty or the index is out of bounds (the lookup is `none`).  This couples
`activeDomainOnCore` to `(domainSchedule, domainScheduleIndexOnCore)` — what makes the
active domain (not just the index) cycle with period `length`. -/
def domainConsistentOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ entry, st.scheduler.domainSchedule[st.scheduler.domainScheduleIndexOnCore c]? = some entry →
    st.scheduler.activeDomainOnCore c = DomainScheduleEntry.domain entry

/-- WS-SM SM5.G.2: the freshly-booted system satisfies the domain-consistency invariant
(empty schedule → the lookup is `none`, vacuous). -/
theorem default_domainConsistentOnCore (c : CoreId) :
    domainConsistentOnCore (default : SystemState) c := by
  intro entry he
  rw [show (default : SystemState).scheduler.domainSchedule = [] from rfl] at he
  simp at he

/-- WS-SM SM5.G.2: a per-core domain rotation **establishes** the domain-consistency
invariant on the rotated core, unconditionally (after a rotation the active domain is
exactly the domain of the entry at the new index). -/
theorem advanceDomainOnCore_establishes_domainConsistentOnCore (st : SystemState) (c : CoreId) :
    domainConsistentOnCore (advanceDomainOnCore st c) c := by
  intro e he
  by_cases hSched : st.scheduler.domainSchedule = []
  · rw [advanceDomainOnCore_empty st c hSched] at he
    rw [hSched] at he
    simp at he
  · rw [advanceDomainOnCore_domainSchedule,
      advanceDomainOnCore_domainScheduleIndexOnCore_self st c hSched] at he
    exact advanceDomainOnCore_rotates st c e he

/-- WS-SM SM5.G.2 (**active-domain cyclic theorem**): from a domain-consistent, in-bounds
state, iterating the rotation `domainSchedule.length` times returns core `c`'s **active
domain** to its starting value — the round-robin cycle closes at the domain level, not
just the index level.  This is the full "every domain runs in turn and the schedule
repeats" statement. -/
theorem advanceDomainOnCore_cyclic_activeDomain (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hidx : st.scheduler.domainScheduleIndexOnCore c < st.scheduler.domainSchedule.length)
    (hConsistent : domainConsistentOnCore st c) :
    (advanceDomainOnCoreN st c st.scheduler.domainSchedule.length).scheduler.activeDomainOnCore c
      = st.scheduler.activeDomainOnCore c := by
  -- The final state's index returns to the start (index cyclic) and its schedule is
  -- unchanged; the final state is domain-consistent (its last step established it).
  have hIdx : (advanceDomainOnCoreN st c st.scheduler.domainSchedule.length).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c := advanceDomainOnCore_cyclic st c hSched hidx
  have hSch : (advanceDomainOnCoreN st c st.scheduler.domainSchedule.length).scheduler.domainSchedule
      = st.scheduler.domainSchedule := advanceDomainOnCoreN_domainSchedule st c _
  have hCons : domainConsistentOnCore (advanceDomainOnCoreN st c st.scheduler.domainSchedule.length) c := by
    obtain ⟨m, hm⟩ : ∃ m, st.scheduler.domainSchedule.length = m + 1 :=
      ⟨st.scheduler.domainSchedule.length - 1, (Nat.sub_add_cancel (List.length_pos_iff.mpr hSched)).symm⟩
    rw [hm, advanceDomainOnCoreN_succ]
    exact advanceDomainOnCore_establishes_domainConsistentOnCore _ c
  -- The entry at the (in-bounds) starting index.
  obtain ⟨e, he⟩ : ∃ e, st.scheduler.domainSchedule[st.scheduler.domainScheduleIndexOnCore c]? = some e :=
    ⟨_, List.getElem?_eq_getElem hidx⟩
  -- Both the final and the starting active domain equal `e.domain`.
  have hFinalAD := hCons e (by rw [hSch, hIdx]; exact he)
  rw [hFinalAD, hConsistent e he]

-- ============================================================================
-- §10  SM5.G.3 — live-transition invariant preservation
-- ============================================================================
--
-- SM5.G's establishment/preservation theorems above are about the *abstract*
-- rotation `advanceDomainOnCore`.  This section lifts them to the **live** domain
-- transitions the kernel actually runs — `switchDomainOnCore` (the rotation, SM5.D.6)
-- and `scheduleDomainOnCore` (the domain tick) — so the SM4.C `activeDomainOnCore_isInDomainSchedule`
-- predicate and the SM5.G `domainScheduleIndexInBoundsOnCore` invariant are proven
-- maintained by the production transitions.  The re-dispatch wrapper
-- (`scheduleEffectiveOnCore`) is domain-irrelevant; the frame lemmas below establish
-- that it touches neither `activeDomainOnCore c` nor `domainSchedule`.

/-- WS-SM SM5.G.3 helper: the idle fallback frames core `c`'s active domain. -/
theorem idleFallbackOnCore_activeDomainOnCore (st : SystemState) (c : CoreId) :
    (idleFallbackOnCore st c).scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c := by
  unfold idleFallbackOnCore
  split
  · exact dispatchIdleOnCore_activeDomainOnCore st c
  · simp [SchedulerState.setCurrentOnCore_activeDomainOnCore]

/-- WS-SM SM5.G.3 helper: the idle fallback frames the domain schedule. -/
theorem idleFallbackOnCore_domainSchedule (st : SystemState) (c : CoreId) :
    (idleFallbackOnCore st c).scheduler.domainSchedule = st.scheduler.domainSchedule := by
  unfold idleFallbackOnCore
  split
  · simp [dispatchIdleOnCore, SchedulerState.setCurrentOnCore, SchedulerState.setRunQueueOnCore,
      restoreIncomingContextOnCore_scheduler]
  · simp [SchedulerState.setCurrentOnCore]

/-- WS-SM SM5.G.3 helper: a successful per-core reschedule frames core `c`'s active
domain (the re-dispatch changes the current thread / run queue / object store, never
the active scheduling domain).  The currently-missing frame the live preservation
needs; proof mirrors `scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore`'s
`hact` step. -/
theorem scheduleEffectiveOnCore_activeDomainOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      rw [idleFallbackOnCore_activeDomainOnCore, saveOutgoingContextOnCore_scheduler_eq]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep
          rw [← hStep]
          simp only [SchedulerState.setCurrentOnCore_activeDomainOnCore, restoreIncomingContextOnCore_scheduler,
            SchedulerState.setRunQueueOnCore_activeDomainOnCore]
          rw [saveOutgoingContextOnCore_scheduler_eq]
        · simp at hStep

/-- WS-SM SM5.G.3 helper: a successful per-core reschedule frames the domain schedule. -/
theorem scheduleEffectiveOnCore_domainSchedule (st : SystemState) (c : CoreId)
    (st' : SystemState) (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.scheduler.domainSchedule = st.scheduler.domainSchedule := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      rw [idleFallbackOnCore_domainSchedule, saveOutgoingContextOnCore_scheduler_eq]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep
          rw [← hStep]
          simp only [SchedulerState.setCurrentOnCore, SchedulerState.setRunQueueOnCore,
            restoreIncomingContextOnCore_scheduler]
          rw [saveOutgoingContextOnCore_scheduler_eq]
        · simp at hStep

/-- WS-SM SM5.G.3 helper: `switchDomainOnCore` frames the domain schedule (it advances
the per-core index, never rewrites the schedule table). -/
theorem switchDomainOnCore_domainSchedule (st : SystemState) (c : CoreId)
    (st' : SystemState) (hStep : switchDomainOnCore st c = .ok st') :
    st'.scheduler.domainSchedule = st.scheduler.domainSchedule := by
  unfold switchDomainOnCore at hStep
  cases hcase : st.scheduler.domainSchedule with
  | nil =>
    rw [hcase] at hStep; simp only [Except.ok.injEq] at hStep; subst hStep
    exact hcase
  | cons hd tl =>
    rw [hcase] at hStep; dsimp only at hStep
    split at hStep
    · simp at hStep
    · simp only [Except.ok.injEq] at hStep; subst hStep
      simp only [SchedulerState.setDomainScheduleIndexOnCore, SchedulerState.setDomainTimeRemainingOnCore,
        SchedulerState.setActiveDomainOnCore, SchedulerState.setCurrentOnCore, SchedulerState.setRunQueueOnCore]
      exact hcase

/-- WS-SM SM5.G.3 helper: `decrementDomainTimeOnCore` frames the domain schedule. -/
theorem decrementDomainTimeOnCore_domainSchedule (st : SystemState) (c : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.domainSchedule = st.scheduler.domainSchedule := by
  simp [decrementDomainTimeOnCore, SchedulerState.setDomainTimeRemainingOnCore]

/-- WS-SM SM5.G.3 (**live rotation transition preserves the membership invariant**):
the operational per-core domain switch `switchDomainOnCore` preserves the SM4.C
`activeDomainOnCore_isInDomainSchedule` predicate.  On a non-empty schedule it
*establishes* it (the new active domain is a real schedule entry's domain); on an empty
schedule it is a no-op (preserved from `hPred`).  This is the production-transition
counterpart of `advanceDomainOnCore_establishes_…`, discharged through the SM5.G.2 full
bridge / `switchDomainOnCore_rotates`. -/
theorem switchDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule
    (st : SystemState) (c : CoreId) (st' : SystemState)
    (hPred : activeDomainOnCore_isInDomainSchedule st c)
    (hStep : switchDomainOnCore st c = .ok st') :
    activeDomainOnCore_isInDomainSchedule st' c := by
  by_cases hSched : st.scheduler.domainSchedule = []
  · rw [switchDomainOnCore_singleDomain_noop st c hSched] at hStep
    injection hStep with hStep'
    subst hStep'
    exact hPred
  · unfold activeDomainOnCore_isInDomainSchedule
    rw [switchDomainOnCore_domainSchedule st c st' hStep]
    right
    have hbound : ((st.scheduler.domainScheduleIndexOnCore c) + 1) % st.scheduler.domainSchedule.length
        < st.scheduler.domainSchedule.length := Nat.mod_lt _ (List.length_pos_iff.mpr hSched)
    obtain ⟨entry, hEntry⟩ :
        ∃ e, st.scheduler.domainSchedule[((st.scheduler.domainScheduleIndexOnCore c) + 1) %
          st.scheduler.domainSchedule.length]? = some e := ⟨_, List.getElem?_eq_getElem hbound⟩
    exact ⟨entry, List.mem_of_getElem? hEntry,
      (switchDomainOnCore_rotates st c st' entry hEntry hSched hStep).symm⟩

/-- WS-SM SM5.G.2 (live rotation preserves the index-bounds invariant): a successful
`switchDomainOnCore` leaves core `c`'s schedule index in bounds. -/
theorem switchDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore
    (st : SystemState) (c : CoreId) (st' : SystemState)
    (hStep : switchDomainOnCore st c = .ok st') :
    domainScheduleIndexInBoundsOnCore st' c := by
  unfold domainScheduleIndexInBoundsOnCore
  rw [switchDomainOnCore_domainSchedule st c st' hStep]
  by_cases hSched : st.scheduler.domainSchedule = []
  · exact Or.inl hSched
  · rw [switchDomainOnCore_domainScheduleIndexOnCore_self st c st' hSched hStep]
    exact Or.inr (Nat.mod_lt _ (List.length_pos_iff.mpr hSched))

/-- WS-SM SM5.G.3 (**live domain-tick transition preserves the membership invariant**):
the operational per-core domain tick `scheduleDomainOnCore` preserves the SM4.C
`activeDomainOnCore_isInDomainSchedule` predicate.  The non-boundary branch is the pure
`decrementDomainTimeOnCore` (frames the active domain + schedule); the boundary branch
is `switchDomainOnCore` (preserves the predicate) followed by the domain-irrelevant
`scheduleEffectiveOnCore` (frames the active domain + schedule).  This wires
`advanceDomainOnCore`'s establishment lemma — via `switchDomainOnCore_rotates` — into
the verification of the *real* live transition. -/
theorem scheduleDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule
    (st : SystemState) (c : CoreId) (st' : SystemState)
    (hPred : activeDomainOnCore_isInDomainSchedule st c)
    (hStep : scheduleDomainOnCore st c = .ok st') :
    activeDomainOnCore_isInDomainSchedule st' c := by
  unfold scheduleDomainOnCore at hStep
  split at hStep
  · cases hsw : switchDomainOnCore st c with
    | error e => rw [hsw] at hStep; simp at hStep
    | ok stMid =>
      rw [hsw] at hStep
      have hMid : activeDomainOnCore_isInDomainSchedule stMid c :=
        switchDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule st c stMid hPred hsw
      unfold activeDomainOnCore_isInDomainSchedule at hMid ⊢
      rw [scheduleEffectiveOnCore_domainSchedule stMid c st' hStep,
        scheduleEffectiveOnCore_activeDomainOnCore stMid c st' hStep]
      exact hMid
  · simp only [Except.ok.injEq] at hStep
    subst hStep
    unfold activeDomainOnCore_isInDomainSchedule at hPred ⊢
    rw [decrementDomainTimeOnCore_domainSchedule, decrementDomainTimeOnCore_activeDomainOnCore]
    exact hPred

-- ============================================================================
-- §11  SM5.G.2/.3 — the SM5.G invariants maintained by the LIVE domain tick
-- ============================================================================
--
-- §10 lifted the SM4.C `activeDomainOnCore_isInDomainSchedule` predicate to the live
-- transitions.  This section does the same for the two SM5.G-introduced invariants —
-- `domainScheduleIndexInBoundsOnCore` (§8, the cyclic theorem's precondition) and
-- `domainConsistentOnCore` (§9, the active-domain cyclic's precondition) — so SM5.I's
-- per-core run loop, which drives `scheduleDomainOnCore`, can carry **both** cyclic
-- theorems' hypotheses across the live domain tick (closing the asymmetry where only
-- `switchDomainOnCore` preserved the index-bounds invariant and neither live
-- transition preserved domain consistency).  The two `…_frame` lemmas reduce each
-- invariant to its read footprint; the per-transition frames discharge them.

/-- WS-SM SM5.G.2 (frame): `domainScheduleIndexInBoundsOnCore` depends only on the
schedule table and core `c`'s index — two states agreeing on those agree on it. -/
theorem domainScheduleIndexInBoundsOnCore_frame {st st' : SystemState} {c : CoreId}
    (hSch : st'.scheduler.domainSchedule = st.scheduler.domainSchedule)
    (hIdx : st'.scheduler.domainScheduleIndexOnCore c = st.scheduler.domainScheduleIndexOnCore c)
    (hInv : domainScheduleIndexInBoundsOnCore st c) :
    domainScheduleIndexInBoundsOnCore st' c := by
  unfold domainScheduleIndexInBoundsOnCore at hInv ⊢
  rw [hSch, hIdx]; exact hInv

/-- WS-SM SM5.G.2 (frame): `domainConsistentOnCore` depends only on the schedule
table, core `c`'s index, and core `c`'s active domain. -/
theorem domainConsistentOnCore_frame {st st' : SystemState} {c : CoreId}
    (hSch : st'.scheduler.domainSchedule = st.scheduler.domainSchedule)
    (hIdx : st'.scheduler.domainScheduleIndexOnCore c = st.scheduler.domainScheduleIndexOnCore c)
    (hAD : st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c)
    (hInv : domainConsistentOnCore st c) :
    domainConsistentOnCore st' c := by
  intro entry he
  rw [hSch, hIdx] at he
  rw [hAD]; exact hInv entry he

/-- WS-SM SM5.G.2 helper: the idle fallback frames core `c`'s schedule index. -/
theorem idleFallbackOnCore_domainScheduleIndexOnCore (st : SystemState) (c : CoreId) :
    (idleFallbackOnCore st c).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c := by
  unfold idleFallbackOnCore
  split
  · simp [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore,
      restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]
  · simp [SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore]

/-- WS-SM SM5.G.2 helper: a successful per-core reschedule frames core `c`'s schedule
index (the re-dispatch changes current / run queue / object store, never the index). -/
theorem scheduleEffectiveOnCore_domainScheduleIndexOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.scheduler.domainScheduleIndexOnCore c = st.scheduler.domainScheduleIndexOnCore c := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      rw [idleFallbackOnCore_domainScheduleIndexOnCore, saveOutgoingContextOnCore_scheduler_eq]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep
          rw [← hStep]
          simp only [SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore, restoreIncomingContextOnCore_scheduler,
            SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]
          rw [saveOutgoingContextOnCore_scheduler_eq]
        · simp at hStep

/-- WS-SM SM5.G.2 helper: `decrementDomainTimeOnCore` frames core `c`'s schedule index. -/
theorem decrementDomainTimeOnCore_domainScheduleIndexOnCore (st : SystemState) (c : CoreId) :
    (decrementDomainTimeOnCore st c).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c := by
  simp [decrementDomainTimeOnCore, SchedulerState.setDomainTimeRemainingOnCore_domainScheduleIndexOnCore]

/-- WS-SM SM5.G.2 (**live domain-tick preserves the index-bounds invariant**):
`scheduleDomainOnCore` maintains `domainScheduleIndexInBoundsOnCore` — the boundary
branch lands the index in bounds (`switchDomainOnCore`, then the index-framing
`scheduleEffectiveOnCore`); the non-boundary branch (`decrementDomainTimeOnCore`)
frames the index.  Together with `default_…` and `advanceDomainOnCore_establishes_…`
this makes the index-bounds invariant a genuinely maintained invariant — so SM5.I can
discharge `advanceDomainOnCore_cyclic_of_inBounds`'s hypothesis across the live tick. -/
theorem scheduleDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore
    (st : SystemState) (c : CoreId) (st' : SystemState)
    (hInv : domainScheduleIndexInBoundsOnCore st c)
    (hStep : scheduleDomainOnCore st c = .ok st') :
    domainScheduleIndexInBoundsOnCore st' c := by
  unfold scheduleDomainOnCore at hStep
  split at hStep
  · cases hsw : switchDomainOnCore st c with
    | error e => rw [hsw] at hStep; simp at hStep
    | ok stMid =>
      rw [hsw] at hStep
      exact domainScheduleIndexInBoundsOnCore_frame
        (scheduleEffectiveOnCore_domainSchedule stMid c st' hStep)
        (scheduleEffectiveOnCore_domainScheduleIndexOnCore stMid c st' hStep)
        (switchDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore st c stMid hsw)
  · simp only [Except.ok.injEq] at hStep; subst hStep
    exact domainScheduleIndexInBoundsOnCore_frame
      (decrementDomainTimeOnCore_domainSchedule st c)
      (decrementDomainTimeOnCore_domainScheduleIndexOnCore st c) hInv

/-- WS-SM SM5.G.2 (live rotation preserves domain consistency): `switchDomainOnCore`
maintains `domainConsistentOnCore` — on a non-empty schedule it *establishes* it (the
new active domain is the domain of the entry at the new index); on an empty schedule it
is a no-op. -/
theorem switchDomainOnCore_preserves_domainConsistentOnCore
    (st : SystemState) (c : CoreId) (st' : SystemState)
    (hCons : domainConsistentOnCore st c)
    (hStep : switchDomainOnCore st c = .ok st') :
    domainConsistentOnCore st' c := by
  by_cases hSched : st.scheduler.domainSchedule = []
  · rw [switchDomainOnCore_singleDomain_noop st c hSched] at hStep
    injection hStep with hStep'
    subst hStep'
    exact hCons
  · intro e he
    rw [switchDomainOnCore_domainSchedule st c st' hStep,
      switchDomainOnCore_domainScheduleIndexOnCore_self st c st' hSched hStep] at he
    rw [switchDomainOnCore_rotates st c st' e he hSched hStep]

/-- WS-SM SM5.G.2 (**live domain-tick preserves domain consistency**):
`scheduleDomainOnCore` maintains `domainConsistentOnCore` — the boundary branch
establishes it (`switchDomainOnCore`) then frames it through the consistency-framing
`scheduleEffectiveOnCore`; the non-boundary branch frames it through
`decrementDomainTimeOnCore`.  So SM5.I can discharge
`advanceDomainOnCore_cyclic_activeDomain`'s consistency hypothesis across the live
tick. -/
theorem scheduleDomainOnCore_preserves_domainConsistentOnCore
    (st : SystemState) (c : CoreId) (st' : SystemState)
    (hCons : domainConsistentOnCore st c)
    (hStep : scheduleDomainOnCore st c = .ok st') :
    domainConsistentOnCore st' c := by
  unfold scheduleDomainOnCore at hStep
  split at hStep
  · cases hsw : switchDomainOnCore st c with
    | error e => rw [hsw] at hStep; simp at hStep
    | ok stMid =>
      rw [hsw] at hStep
      exact domainConsistentOnCore_frame
        (scheduleEffectiveOnCore_domainSchedule stMid c st' hStep)
        (scheduleEffectiveOnCore_domainScheduleIndexOnCore stMid c st' hStep)
        (scheduleEffectiveOnCore_activeDomainOnCore stMid c st' hStep)
        (switchDomainOnCore_preserves_domainConsistentOnCore st c stMid hCons hsw)
  · simp only [Except.ok.injEq] at hStep; subst hStep
    exact domainConsistentOnCore_frame
      (decrementDomainTimeOnCore_domainSchedule st c)
      (decrementDomainTimeOnCore_domainScheduleIndexOnCore st c)
      (decrementDomainTimeOnCore_activeDomainOnCore st c c) hCons

end SeLe4n.Kernel
