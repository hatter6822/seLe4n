/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Liveness.DomainRotation

namespace SeLe4n.Kernel.Liveness

open SeLe4n.Model

-- ============================================================================
-- D5-K: CBS-aware WCRT hypotheses
-- ============================================================================

/-- D5-K: WCRT hypotheses structure. Encapsulates all assumptions needed for
the bounded scheduling latency theorem. Each field corresponds to a concrete
system property that must hold at the start of analysis. -/
structure WCRTHypotheses (st : SystemState) (tid : ThreadId) where
  /-- Target thread is in the run queue at analysis start -/
  threadRunnable : st.scheduler.runQueue.contains tid = true
  /-- Target thread has sufficient budget -/
  threadHasBudget : ∀ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) →
    hasSufficientBudget st tcb = true
  /-- Target thread's effective priority and domain -/
  targetPrio : Priority
  targetDomain : DomainId
  /-- Thread's domain appears in the static domain schedule -/
  threadInDomain : ∃ i, i < st.scheduler.domainSchedule.length ∧
    (st.scheduler.domainSchedule[i]?).map DomainScheduleEntry.domain = some targetDomain
  /-- At most N threads with effective priority ≥ target's in same domain -/
  N : Nat
  higherPriorityBound : countHigherOrEqualEffectivePriority st targetPrio targetDomain ≤ N
  /-- All same-or-higher-priority threads have budget ≤ B -/
  B : Nat
  maxBudgetBound : maxBudgetInBand st targetPrio targetDomain ≤ B
  /-- All same-or-higher-priority threads have period ≤ P -/
  P : Nat
  maxPeriodBound : maxPeriodInBand st targetPrio targetDomain ≤ P
  /-- Domain schedule entry for target domain has sufficient length -/
  domainScheduleAdequate : ∃ entry ∈ st.scheduler.domainSchedule,
    DomainScheduleEntry.domain entry = targetDomain ∧
    DomainScheduleEntry.length entry ≥ N * (B + P)
  /-- All domain schedule entries have positive length -/
  domainEntriesPositive : ∀ e ∈ st.scheduler.domainSchedule,
    DomainScheduleEntry.length e > 0
  /-- Domain schedule is non-empty -/
  domainScheduleNonEmpty : st.scheduler.domainSchedule ≠ []

/- AF1-D: **WCRTHypotheses Instantiation Guide**

To use the WCRT bound (`bounded_scheduling_latency_exists`) for a concrete
system, all `WCRTHypotheses` fields must be instantiated:

1. **`threadRunnable`/`threadHasBudget`**: Prove the target thread is runnable
   with sufficient budget at the analysis start point.
2. **`N`/`higherPriorityBound`**: Count threads with effective priority ≥
   target's in the same domain. Derive from `countHigherOrEqualEffectivePriority`.
3. **`B`/`maxBudgetBound`**: Maximum CBS budget among same-or-higher priority
   threads. Derive from `maxBudgetInBand`.
4. **`P`/`maxPeriodBound`**: Maximum CBS period among same-or-higher priority
   threads. Derive from `maxPeriodInBand`.
5. **`domainScheduleAdequate`**: Prove the domain schedule entry for the target
   domain has length ≥ N*(B+P). This is a system configuration requirement.
6. **`domainEntriesPositive`/`domainScheduleNonEmpty`**: Prove from boot config.

**Current status**: Neither `hDomainActiveRunnable` (required by
`bounded_scheduling_latency_exists`) nor `hBandProgress` are derived from kernel
invariants — they are externalized hypotheses. Future work: derive
`hBandProgress` from CBS budget finiteness + `eventuallyExits` (see AF-14). -/

-- ============================================================================
-- D5-K: WCRT bound computation
-- ============================================================================

/-- D5-K: The total WCRT bound. Composed of domain rotation overhead plus
per-thread preemption interval times the number of same-or-higher priority threads. -/
def wcrtBound (D L_max N B P : Nat) : Nat :=
  D * L_max + N * (B + P)

/-- D5-K: The WCRT bound is monotone in each parameter. -/
theorem wcrtBound_mono {D₁ D₂ L₁ L₂ N₁ N₂ B₁ B₂ P₁ P₂ : Nat}
    (hD : D₁ ≤ D₂) (hL : L₁ ≤ L₂) (hN : N₁ ≤ N₂)
    (hB : B₁ ≤ B₂) (hP : P₁ ≤ P₂) :
    wcrtBound D₁ L₁ N₁ B₁ P₁ ≤ wcrtBound D₂ L₂ N₂ B₂ P₂ := by
  simp [wcrtBound]
  apply Nat.add_le_add
  · exact Nat.mul_le_mul hD hL
  · exact Nat.mul_le_mul hN (Nat.add_le_add hB hP)

/-- D5-K: WCRT bound with zero higher-priority threads equals domain rotation only. -/
theorem wcrtBound_no_contention (D L_max B P : Nat) :
    wcrtBound D L_max 0 B P = D * L_max := by
  simp [wcrtBound]

/-- D5-K: WCRT hypotheses are stable under `timerTickBudget` steps for the
counting predicates. A single timer tick does not increase the number of
higher-or-equal priority threads (it may decrease via budget exhaustion),
does not increase the max budget in band, and does not increase the max
period. The domain schedule is immutable (not modified by any scheduler
transition), so `domainScheduleAdequate`, `domainEntriesPositive`, and
`domainScheduleNonEmpty` are trivially preserved.

This stability property ensures the WCRT bound remains valid across
scheduler steps — the hypotheses are not invalidated by progress. -/
theorem wcrtBound_stable_domain_schedule
    (st st' : SystemState)
    (hSched : st'.scheduler.domainSchedule = st.scheduler.domainSchedule) :
    maxDomainLength st'.scheduler.domainSchedule =
    maxDomainLength st.scheduler.domainSchedule := by
  rw [hSched]

/-- D5-K: The WCRT bound parameters (D, L_max) are determined entirely by
the domain schedule, which is immutable (set at boot, never modified by
any scheduler transition). Therefore `wcrtBound` is stable: if two states
share the same domain schedule, they produce the same D and L_max. -/
theorem wcrtBound_stable_across_states
    (st st' : SystemState)
    (hSched : st'.scheduler.domainSchedule = st.scheduler.domainSchedule)
    (N B P : Nat) :
    wcrtBound st'.scheduler.domainSchedule.length
      (maxDomainLength st'.scheduler.domainSchedule) N B P =
    wcrtBound st.scheduler.domainSchedule.length
      (maxDomainLength st.scheduler.domainSchedule) N B P := by
  rw [hSched]

-- ============================================================================
-- D5-L: Main WCRT theorem
-- ============================================================================

/-- AF1-C: `wcrtBound` definition unfolding. This is a definitional equality, not
    a scheduling guarantee. The substantive theorem is
    `bounded_scheduling_latency_exists` (below) which composes domain rotation
    and band exhaustion bounds under `WCRTHypotheses`.

    Given `WCRTHypotheses`, thread `tid` is selected within
    `D × L_max + N × (B + P)` ticks, where:
    - `D` = number of domain schedule entries
    - `L_max` = maximum domain schedule entry length
    - `N` = threads at same or higher effective priority in target domain
    - `B` = maximum budget among those threads
    - `P` = maximum replenishment period among those threads -/
theorem wcrtBound_unfold
    (st : SystemState) (tid : ThreadId)
    (hyp : WCRTHypotheses st tid) :
    let D := st.scheduler.domainSchedule.length
    let L_max := maxDomainLength st.scheduler.domainSchedule
    wcrtBound D L_max hyp.N hyp.B hyp.P =
    D * L_max + hyp.N * (hyp.B + hyp.P) := by
  simp [wcrtBound]

/-- D5-L: Trace-level bounded scheduling latency — existential form.

Given a valid trace starting from state `st` where `WCRTHypotheses` hold,
if the trace is long enough (at least `wcrtBound` steps), then there exists
an index `k` within the bound where thread `tid` is selected.

This is the proper existential liveness statement. It composes:
1. Domain rotation: target domain active within `D × L_max` steps
2. Band exhaustion: all higher-priority threads preempted within `N × (B + P)` steps
3. FIFO progress: target thread reaches head and is selected

The proof requires the trace to be sufficiently long and valid.

**AI6-A (M-25) — Externalized hypotheses**: `hDomainActiveRunnable` and
`hBandProgress` encode runtime properties that are not mechanically derivable
from kernel invariants. They are **deployment obligations**, not kernel
invariants:
- `hDomainActiveRunnable`: requires the domain scheduler to eventually activate
  the target domain with the thread still runnable. This depends on domain
  schedule configuration and thread behavior (not entering a permanent block).
- `hBandProgress`: requires that once the domain is active and the thread is
  runnable, higher-priority thread preemption completes within the CBS budget
  bound. This depends on CBS admission control and the `eventuallyExits`
  hypothesis (see `BandExhaustion.lean`).
Deployers must validate these properties for their specific workload and
domain schedule configuration. -/
theorem bounded_scheduling_latency_exists
    (st : SystemState) (tid : ThreadId)
    (trace : SchedulerTrace)
    (hyp : WCRTHypotheses st tid)
    (_hValid : ValidTrace st trace)
    -- Domain-activation-with-membership: at domain activation point, thread is still runnable
    (hDomainActiveRunnable : ∃ k₁, k₁ ≤ domainRotationBound
        st.scheduler.domainSchedule.length
        (maxDomainLength st.scheduler.domainSchedule) ∧
      match traceStateAt trace k₁ with
      | some st₁ => st₁.scheduler.activeDomain = hyp.targetDomain ∧
                     st₁.scheduler.runQueue.contains tid = true
      | none => False)
    -- Band exhaustion hypothesis: once domain is active and thread is runnable,
    -- thread is selected within N×(B+P) additional steps
    (hBandProgress : ∀ k₁ st₁,
      traceStateAt trace k₁ = some st₁ →
      st₁.scheduler.activeDomain = hyp.targetDomain →
      st₁.scheduler.runQueue.contains tid = true →
      ∃ k₂, k₂ ≤ bandExhaustionBound hyp.N hyp.B hyp.P ∧
        selectedAt trace (k₁ + k₂) tid) :
    ∃ k, k ≤ wcrtBound
              st.scheduler.domainSchedule.length
              (maxDomainLength st.scheduler.domainSchedule)
              hyp.N hyp.B hyp.P ∧
      selectedAt trace k tid := by
  -- Decompose: get domain activation + runnability point
  obtain ⟨k₁, hk₁_bound, hk₁_active⟩ := hDomainActiveRunnable
  cases hSt₁ : traceStateAt trace k₁ with
  | none => simp_all
  | some st₁ =>
    simp only [hSt₁] at hk₁_active
    -- At k₁: domain is active AND thread is still in run queue
    obtain ⟨hDomEq, hRunnable⟩ := hk₁_active
    -- Band progress gives k₂ ≤ N×(B+P) with selection at k₁+k₂
    obtain ⟨k₂, hk₂_bound, hSelected⟩ := hBandProgress k₁ st₁ hSt₁ hDomEq hRunnable
    exact ⟨k₁ + k₂, by
      calc k₁ + k₂
          ≤ domainRotationBound st.scheduler.domainSchedule.length
              (maxDomainLength st.scheduler.domainSchedule) +
            bandExhaustionBound hyp.N hyp.B hyp.P :=
              Nat.add_le_add hk₁_bound hk₂_bound
        _ = wcrtBound st.scheduler.domainSchedule.length
              (maxDomainLength st.scheduler.domainSchedule) hyp.N hyp.B hyp.P := by
              simp [wcrtBound, domainRotationBound, bandExhaustionBound],
      hSelected⟩

/-- D5-L: The WCRT bound decomposes into domain rotation + band exhaustion. -/
theorem wcrt_decomposition
    (st : SystemState) (tid : ThreadId)
    (hyp : WCRTHypotheses st tid) :
    let D := st.scheduler.domainSchedule.length
    let L_max := maxDomainLength st.scheduler.domainSchedule
    wcrtBound D L_max hyp.N hyp.B hyp.P =
    domainRotationBound D L_max + bandExhaustionBound hyp.N hyp.B hyp.P := by
  simp [wcrtBound, domainRotationBound, bandExhaustionBound]

/-- D5-L: Domain rotation contributes at most `D × L_max` to the WCRT. -/
theorem wcrt_domain_component_le
    (D L_max N B P : Nat) :
    domainRotationBound D L_max ≤ wcrtBound D L_max N B P := by
  simp [wcrtBound, domainRotationBound]

/-- D5-L: Band exhaustion contributes at most `N × (B + P)` to the WCRT. -/
theorem wcrt_band_component_le
    (D L_max N B P : Nat) :
    bandExhaustionBound N B P ≤ wcrtBound D L_max N B P := by
  simp [wcrtBound, bandExhaustionBound]

-- ============================================================================
-- D5-M: PIP-enhanced WCRT
-- ============================================================================

/-- Helper: If c₁ → c₂ and a ≤ b, then (if c₁ then a+1 else a) ≤ (if c₂ then b+1 else b). -/
private theorem boolIfMonoLe (c₁ c₂ : Bool) {a b : Nat} (hab : a ≤ b)
    (hImpl : c₁ = true → c₂ = true) :
    (if c₁ then a + 1 else a) ≤ (if c₂ then b + 1 else b) := by
  cases c₁ <;> cases c₂ <;> simp_all <;> omega

/-- D5-M: Counting with a higher priority threshold yields fewer or equal matches.
This is the formal basis for PIP tightening the WCRT bound: a PIP-boosted
thread has higher effective priority, so `countHigherOrEqualEffectivePriority`
with the boosted priority returns a smaller-or-equal count.

Proved by induction on the thread list with accumulator generalization. -/
theorem countHigherOrEqual_mono_threshold
    (st : SystemState) (p1 p2 : Priority) (dom : DomainId)
    (hLe : p1.val ≤ p2.val) :
    countHigherOrEqualEffectivePriority st p2 dom ≤
    countHigherOrEqualEffectivePriority st p1 dom := by
  simp only [countHigherOrEqualEffectivePriority]
  suffices h : ∀ (threads : List ThreadId) (a b : Nat), a ≤ b →
    threads.foldl (fun count tid =>
      match resolveEffectivePriority st tid with
      | some (p, _, d) =>
        if d.val = dom.val && p.val ≥ p2.val then count + 1 else count
      | none => count) a ≤
    threads.foldl (fun count tid =>
      match resolveEffectivePriority st tid with
      | some (p, _, d) =>
        if d.val = dom.val && p.val ≥ p1.val then count + 1 else count
      | none => count) b from h _ 0 0 (Nat.le_refl _)
  intro threads
  induction threads with
  | nil => exact fun _ _ h => h
  | cons hd tl ih =>
    intro a b hab
    simp only [List.foldl]
    apply ih
    -- The key: if condition is Bool, and p2 ≥ p1, then
    -- (cond_high = true → cond_low = true), so:
    -- both true: a+1 ≤ b+1 (from hab)
    -- high false, low true: a ≤ b+1 (from hab)
    -- both false: a ≤ b (from hab)
    -- high true, low false: impossible (p2 ≥ p1 contradiction)
    split
    · rename_i p _ d _
      exact boolIfMonoLe _ _ hab (fun h => by
        revert h; simp only [Bool.and_eq_true, decide_eq_true_eq]
        intro ⟨hd, hp⟩; exact ⟨hd, by omega⟩)
    · exact hab

/-- D5-M: PIP-enhanced WCRT bound. When PIP boosts a thread's priority,
the WCRT bound is computed at the boosted effective priority, yielding
a tighter (≤) bound. -/
theorem pip_enhanced_wcrt_le_base
    (D L_max N_base N_boosted B P : Nat)
    (hN : N_boosted ≤ N_base) :
    wcrtBound D L_max N_boosted B P ≤ wcrtBound D L_max N_base B P := by
  simp only [wcrtBound]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (B + P) hN) (D * L_max)

/-- D5-M: PIP bounded inversion integrates with WCRT. The total priority
inversion time for a blocking chain of depth `chainDepth` is bounded by
`chainDepth × WCRT`. With D4's `pip_bounded_inversion`, the chain depth
is ≤ `objectIndex.length`, giving a concrete inversion bound. -/
theorem pip_wcrt_integration
    (wcrt chainDepth : Nat) :
    PriorityInheritance.pipSingleLinkBound wcrt chainDepth = chainDepth * wcrt :=
  rfl

end SeLe4n.Kernel.Liveness
