-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR2.3: PRODUCTION.  The SM5.H replenish-queue affinity invariant and the
-- migration lemmas that establish it, hoisted out of the staged
-- `Scheduler/Operations/PerCoreCbs.lean` so the **live** donation paths can be
-- held to it.  Enters the production import closure through the cross-core
-- `.call` / `.reply` donation arms (`IPC/Operations/Donation.lean`) and the
-- `.tcbSuspend` cancellation arm (`IPC/CrossCore/Cancellation.lean`).

import SeLe4n.Kernel.Scheduler.Operations.Core

/-!
# WS-SM SM5.H / WS-RR RR2 — replenish-queue affinity, in production

An SC's pending CBS replenishments live on **its bound thread's home core's**
queue: `replenishOnCore` writes `replenishQueueOnCore c` for the core the SC's
bound thread runs on, and only that core's timer tick drains them.  The
predicate saying so is `replenishQueueAffinityConsistentOnCore`; the operation
that restores it when a SC changes hands is `migrateSchedContextReplenishment`
(`Scheduler/Operations/Core.lean`).

## Why this module exists

Both halves used to live in the **staged** `PerCoreCbs.lean`, which production
may not import.  That was tolerable while the only mover was the staged
`.tcbSetAffinity` composite; it stopped being tolerable at WS-RR RR2, where the
live cross-core `.call` and `.reply` donation arms became movers too — a SC
donated to a server on another core keeps its replenishments on the *donor's*
core unless the donation migrates them, which is precisely the invariant this
predicate names.  A production theorem needs a production predicate.

Hoisting also **removes a duplicate rather than adding one**: the production
`.tcbSuspend` cancellation arm carried its own hand-written twins of five of
these frame lemmas (`migrateSchedContextReplenishment_{objects,self,runQueue_
current,replenishQueue_other,from}_eq`) for exactly the same reason.  Those are
gone; `Cancellation.lean` consumes the canonical forms below, so the migration's
frame is stated once and the two readings cannot drift.

## What is here

* §1 — the affinity predicate (`…OnCore`, `…_smp`), its boot-state discharge and
  its frame.
* §2 — the `ReplenishQueue` membership-decomposition lemmas the preservation
  proofs rest on.
* §3 — the migration's frames: it writes **only** the two replenish-queue slots.
* §4 — the migration genuinely *moves* the SC's entries (source purged,
  destination provenance).
* §5 — the migration establishes affinity consistency on the destination,
  preserves it on the source, and frames it everywhere else.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  SM5.H.5 — the affinity-consistency invariant
-- ============================================================================

/-- WS-SM SM5.H.5 (plan §3.8 Theorem 3.8.1): core `c`'s replenish queue is
**affinity-consistent** — every SchedContext with a pending replenishment on
core `c` is bound to a thread homed on core `c`.  Formally: for every entry
`(scId, t)` of `replenishQueueOnCore c`, if `scId` resolves to a SchedContext
whose `boundThread` is `tid`, then that thread's wake target
(`determineTargetCore`, the SM5.C.9 home-core rule) is `c`.

This is the per-core CBS analogue of the SM4.C
`schedContextRunQueueConsistent_perCore` (run queue ↔ budget): it connects the
per-core *replenish* queue to per-thread CPU placement, so a thread's
budget-refill schedule lives on the core the thread will wake onto.  It is the
invariant the SM5.H.4 migration restores — a SchedContext that changes hands
(affinity change, or a WS-RR RR2 cross-core donation) drags its replenishments
to the new home core.

The literal `cpuAffinity = some c` of the §3.8 pseudocode is generalised to
`determineTargetCore st tid = c`: for a thread bound to `some c` it is exactly
`cpuAffinity = some c`, while for a SchedContext-bound but affinity-unbound
thread (`cpuAffinity = none`) it correctly maps to `bootCoreId` (the boot core
homes unbound threads, SM5.C.9) — the literal form would wrongly forbid such
threads from holding a SchedContext at all. -/
def replenishQueueAffinityConsistentOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (scId : SchedContextId) (t : Nat),
    (scId, t) ∈ (st.scheduler.replenishQueueOnCore c).entries →
    ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid →
        determineTargetCore st tid = c

/-- WS-SM SM5.H.5: the SMP-wide affinity-consistency invariant — every core's
replenish queue is affinity-consistent. -/
def replenishQueueAffinityConsistent_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, replenishQueueAffinityConsistentOnCore st c

/-- WS-SM SM5.H.5: the SMP form extracts the per-core form at any core. -/
theorem replenishQueueAffinityConsistent_smp_at (st : SystemState)
    (h : replenishQueueAffinityConsistent_smp st) (c : CoreId) :
    replenishQueueAffinityConsistentOnCore st c := h c

/-- WS-SM SM5.H.5: the freshly-booted system is affinity-consistent on every core
(vacuous — the default replenish queue is empty). -/
theorem default_replenishQueueAffinityConsistentOnCore (c : CoreId) :
    replenishQueueAffinityConsistentOnCore (default : SystemState) c := by
  intro scId t hMem _ _ _ _
  have hRepl : (default : SystemState).scheduler.replenishQueueOnCore c
      = SeLe4n.Kernel.ReplenishQueue.empty := (default_state_perCoreInitialized c).2.2.1
  rw [hRepl] at hMem
  simp [SeLe4n.Kernel.ReplenishQueue.empty] at hMem

/-- WS-SM SM5.H.5: the freshly-booted system is SMP-affinity-consistent. -/
theorem default_replenishQueueAffinityConsistent_smp :
    replenishQueueAffinityConsistent_smp (default : SystemState) :=
  fun c => default_replenishQueueAffinityConsistentOnCore c

/-- WS-SM SM5.H.5 / WS-RR RR2.20 (frame, congruence form): the affinity-consistency
invariant on core `c` makes exactly three readings — core `c`'s replenish queue,
`getSchedContext?`, and `determineTargetCore` — so a state agreeing on those
three agrees on the predicate, whatever else it changed.

The `_frame` form below asks for whole-`objects` equality, which is strictly
stronger and excludes precisely the transitions that most need the frame: a PIP
boost rewrites one TCB's `pipBoost`, so `objects` differs while all three
readings agree. -/
theorem replenishQueueAffinityConsistentOnCore_congr {st st' : SystemState} {c : CoreId}
    (hRepl : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (hSc : ∀ scId, st'.getSchedContext? scId = st.getSchedContext? scId)
    (hTgt : ∀ tid, determineTargetCore st' tid = determineTargetCore st tid) :
    replenishQueueAffinityConsistentOnCore st' c ↔
    replenishQueueAffinityConsistentOnCore st c := by
  unfold replenishQueueAffinityConsistentOnCore
  simp only [hRepl, hSc, hTgt]

/-- WS-SM SM5.H.5 (frame): the affinity-consistency invariant on core `c` reads
only core `c`'s replenish queue plus the object store (via `getSchedContext?` and
`determineTargetCore`, both pure object-store reads).  A state agreeing on those
agrees on the predicate. -/
theorem replenishQueueAffinityConsistentOnCore_frame {st st' : SystemState} {c : CoreId}
    (hRepl : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (hObj : st'.objects = st.objects) :
    replenishQueueAffinityConsistentOnCore st' c ↔
    replenishQueueAffinityConsistentOnCore st c :=
  replenishQueueAffinityConsistentOnCore_congr hRepl
    (fun scId => by unfold SystemState.getSchedContext?; rw [hObj])
    (fun tid => by unfold determineTargetCore SystemState.getTcb?; rw [hObj])

/-- WS-RR (bind/unbind affinity closure) — transfer form: affinity-consistency
on core `c` reads the queue's entries, each SchedContext's `boundThread`
*projection*, and each thread's home core — so it transfers backwards along an
entry-subset, a `boundThread`-projection agreement, and a home-core agreement.

Strictly weaker premises than `_congr`: the `.map (·.boundThread)` form matters
because the reschedule receiver's object write is a register-context TCB save —
it frames the projection (and every home core) while the whole `objects` store
differs, which is exactly the shape `_frame` excludes and `_congr`'s full
`getSchedContext?` equality does not need but its consumers would have to
re-derive per SchedContext field. -/
theorem replenishQueueAffinityConsistentOnCore_transfer (st base : SystemState) (c : CoreId)
    (hSub : ∀ e, e ∈ (base.scheduler.replenishQueueOnCore c).entries →
                 e ∈ (st.scheduler.replenishQueueOnCore c).entries)
    (hBound : ∀ scId, (base.getSchedContext? scId).map (·.boundThread)
                    = (st.getSchedContext? scId).map (·.boundThread))
    (hTgt : ∀ tid, determineTargetCore base tid = determineTargetCore st tid)
    (hCons : replenishQueueAffinityConsistentOnCore st c) :
    replenishQueueAffinityConsistentOnCore base c := by
  intro scId t hMem sc hSc tid hTid
  have hMapEq := hBound scId
  rw [hSc] at hMapEq
  cases hB : st.getSchedContext? scId with
  | none => rw [hB] at hMapEq; simp at hMapEq
  | some scS =>
    rw [hB] at hMapEq
    simp only [Option.map_some] at hMapEq
    rw [hTgt tid]
    exact hCons scId t (hSub _ hMem) scS hB tid
      (by rw [← Option.some.inj hMapEq]; exact hTid)

-- ============================================================================
-- §2  Membership decomposition for `ReplenishQueue.insertSorted` / `.remove`
-- ============================================================================

/-- WS-SM SM5.H: a member of `insertSorted entries scId t` is either the freshly
inserted entry `(scId, t)` or an original entry of `entries`.  The reverse of the
existing `ReplenishQueue.mem_insertSorted` / `subset_insertSorted`. -/
theorem mem_insertSorted_iff (entries : List (SchedContextId × Nat))
    (scId : SchedContextId) (t : Nat) (e : SchedContextId × Nat) :
    e ∈ ReplenishQueue.insertSorted entries scId t ↔ (e = (scId, t) ∨ e ∈ entries) := by
  induction entries with
  | nil => simp [ReplenishQueue.insertSorted]
  | cons hd tail ih =>
    obtain ⟨hId, hTime⟩ := hd
    unfold ReplenishQueue.insertSorted
    split
    · -- `t < hTime`: result is `(scId, t) :: (hId, hTime) :: tail`; both sides
      -- normalise to the same 3-way disjunction.
      simp only [List.mem_cons]
    · -- `¬ t < hTime`: result is `(hId, hTime) :: insertSorted tail …`; close the
      -- or-reassociation explicitly (`tauto` is unavailable in the core toolchain).
      simp only [List.mem_cons, ih]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- WS-SM SM5.H: a member of `rq.remove scId`'s entries is an original member of
`rq.entries` whose key is *not* `scId` (the filtered-out key). -/
theorem mem_remove_entries {rq : ReplenishQueue} {scId : SchedContextId}
    {e : SchedContextId × Nat} (h : e ∈ (rq.remove scId).entries) :
    e ∈ rq.entries ∧ e.1 ≠ scId := by
  simp only [ReplenishQueue.remove] at h
  have h' := List.mem_filter.mp h
  refine ⟨h'.1, ?_⟩
  intro hEq
  have hbeq : (e.1 == scId) = true := by rw [hEq]; exact beq_self_eq_true _
  simp [hbeq] at h'

/-- WS-SM SM5.H.4: a member of a fold-of-inserts (all keyed by `scId`) is either
an original member of the seed queue `toQ`, or one of the inserted entries
`(scId, x.2)` for some `x` in the moved list.  The provenance lemma the migration
preservation proofs decompose membership with. -/
theorem mem_foldl_insert_provenance (moved : List (SchedContextId × Nat))
    (scId : SchedContextId) (e : SchedContextId × Nat) :
    ∀ (toQ : ReplenishQueue),
      e ∈ (moved.foldl (fun q x => q.insert scId x.2) toQ).entries →
      e ∈ toQ.entries ∨ ∃ x ∈ moved, e = (scId, x.2) := by
  induction moved with
  | nil => intro toQ h; exact Or.inl h
  | cons hd tail ih =>
    intro toQ h
    rw [List.foldl_cons] at h
    rcases ih (toQ.insert scId hd.2) h with h' | ⟨x, hxMem, hxEq⟩
    · rcases (mem_insertSorted_iff _ scId hd.2 e).mp h' with hEq | hMem
      · exact Or.inr ⟨hd, List.mem_cons_self .., hEq⟩
      · exact Or.inl hMem
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hxMem, hxEq⟩

-- ============================================================================
-- §3  SM5.H.4 — the migration's frames
-- ============================================================================
--
-- `migrateSchedContextReplenishment st scId fromCore toCore` (production def in
-- `Scheduler/Operations/Core.lean`) removes every `(scId, _)` entry from
-- `fromCore`'s queue and re-inserts each at its original eligibility time into
-- `toCore`'s — a fold of `ReplenishQueue.insert`s — and is a no-op when the two
-- cores coincide.  It writes **only** the two replenish-queue slots: the object
-- store, every run queue, every current slot and every other per-core slot are
-- untouched, so `getSchedContext?` / `determineTargetCore` read through it.

/-- WS-SM SM5.H.4: a self-migration (`fromCore = toCore`) is the identity. -/
@[simp] theorem migrateSchedContextReplenishment_noop (st : SystemState)
    (scId : SchedContextId) (c : CoreId) :
    migrateSchedContextReplenishment st scId c c = st := by
  unfold migrateSchedContextReplenishment; rw [if_pos rfl]

/-- WS-SM SM5.H.4: the migration never touches the object store. -/
@[simp] theorem migrateSchedContextReplenishment_objects (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).objects = st.objects := by
  unfold migrateSchedContextReplenishment; split <;> rfl

/-- WS-SM SM5.H.4: the migration never advances the machine timer. -/
@[simp] theorem migrateSchedContextReplenishment_machine (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).machine = st.machine := by
  unfold migrateSchedContextReplenishment; split <;> rfl

/-- WS-SM SM5.H.4: the migration frames every SchedContext resolution. -/
theorem migrateSchedContextReplenishment_getSchedContext? (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (scId' : SchedContextId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).getSchedContext? scId'
      = st.getSchedContext? scId' := by
  unfold SystemState.getSchedContext?; rw [migrateSchedContextReplenishment_objects]

/-- WS-SM SM5.H.4: the migration frames every thread's home core. -/
theorem migrateSchedContextReplenishment_determineTargetCore (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (tid : SeLe4n.ThreadId) :
    determineTargetCore (migrateSchedContextReplenishment st scId fromCore toCore) tid
      = determineTargetCore st tid := by
  unfold determineTargetCore SystemState.getTcb?; rw [migrateSchedContextReplenishment_objects]

/-- WS-SM SM5.H.4: the migration frames every thread's TCB resolution. -/
theorem migrateSchedContextReplenishment_getTcb? (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (tid : SeLe4n.ThreadId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).getTcb? tid
      = st.getTcb? tid := by
  unfold SystemState.getTcb?; rw [migrateSchedContextReplenishment_objects]

/-- WS-SM SM5.H.4 / SM6.E: the migration never disturbs any core's run queue or
current slot — it writes only replenish-queue slots. -/
theorem migrateSchedContextReplenishment_runQueue_current_eq (st : SystemState)
    (scId : SchedContextId) (fromCore toCore c : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.runQueueOnCore c
        = st.scheduler.runQueueOnCore c
    ∧ (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.currentOnCore c
        = st.scheduler.currentOnCore c := by
  unfold migrateSchedContextReplenishment
  split
  · exact ⟨rfl, rfl⟩
  · constructor <;> simp

/-- WS-SM SM5.H.4: core `toCore`'s post-migration replenish queue is the fold of
`scId`-inserts onto its pre-state queue (when `fromCore ≠ toCore`). -/
theorem migrateSchedContextReplenishment_replenishQueueOnCore_to (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore toCore
      = ((st.scheduler.replenishQueueOnCore fromCore).entries.filter (fun e => e.1 == scId)).foldl
          (fun q e => q.insert scId e.2) (st.scheduler.replenishQueueOnCore toCore) := by
  unfold migrateSchedContextReplenishment; rw [if_neg h]
  exact SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self _ _ _

/-- WS-SM SM5.H.4: core `fromCore`'s post-migration replenish queue is its
pre-state queue with all `scId` entries removed (when `fromCore ≠ toCore`). -/
theorem migrateSchedContextReplenishment_replenishQueueOnCore_from (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore fromCore
      = (st.scheduler.replenishQueueOnCore fromCore).remove scId := by
  unfold migrateSchedContextReplenishment; rw [if_neg h]
  rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ (Ne.symm h)]
  exact SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self _ _ _

/-- WS-SM SM5.H.4: a core `c'` other than `fromCore` / `toCore` has its replenish
queue untouched by the migration. -/
theorem migrateSchedContextReplenishment_replenishQueueOnCore_other (st : SystemState)
    (scId : SchedContextId) (fromCore toCore c' : CoreId)
    (hFrom : fromCore ≠ c') (hTo : toCore ≠ c') :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  unfold migrateSchedContextReplenishment
  by_cases h : fromCore = toCore
  · rw [if_pos h]
  · rw [if_neg h]
    rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hTo,
        SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hFrom]

-- ============================================================================
-- §4  SM5.H.4 — the migration genuinely *moves* the SchedContext's entries
-- ============================================================================

/-- WS-SM SM5.H.4: after a migration (`fromCore ≠ toCore`), **no** `scId`
replenishment remains in `fromCore`'s queue — they were all removed. -/
theorem migrateSchedContextReplenishment_fromCore_excludes_scId (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore) (t : Nat) :
    (scId, t) ∉ ((migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore fromCore).entries := by
  rw [migrateSchedContextReplenishment_replenishQueueOnCore_from st scId fromCore toCore h]
  intro hMem
  exact (mem_remove_entries hMem).2 rfl

/-- WS-SM SM5.H.4: every entry in `toCore`'s post-migration queue either was
already there, or is one of `scId`'s migrated entries (a `(scId, _)` pair drawn
from `fromCore`'s pre-state queue).  The membership decomposition the affinity /
pipeline preservation proofs use. -/
theorem migrateSchedContextReplenishment_mem_toCore (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore)
    (e : SchedContextId × Nat)
    (hMem : e ∈ ((migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore toCore).entries) :
    e ∈ (st.scheduler.replenishQueueOnCore toCore).entries ∨
      (e.1 = scId ∧ e ∈ (st.scheduler.replenishQueueOnCore fromCore).entries) := by
  rw [migrateSchedContextReplenishment_replenishQueueOnCore_to st scId fromCore toCore h] at hMem
  rcases mem_foldl_insert_provenance _ scId e _ hMem with hOld | ⟨x, hxMem, hxEq⟩
  · exact Or.inl hOld
  · have hxFilt := List.mem_filter.mp hxMem
    have hxKey : x.1 = scId := eq_of_beq hxFilt.2
    have hex : e = x := by rw [hxEq, ← hxKey]
    exact Or.inr ⟨by rw [hxEq], hex ▸ hxFilt.1⟩

-- ============================================================================
-- §5  SM5.H.5 — migration-level affinity behaviour
-- ============================================================================

/-- WS-SM SM5.H.4 / SM5.H.5: the migration *establishes* affinity consistency on
the destination core `toCore`, given `toCore`'s pre-existing entries are
consistent (`hConsTo`) and the migrated SchedContext is itself homed on `toCore`
(`hHome` — its bound thread's `determineTargetCore` is `toCore`).  The migrated
entries are precisely `scId`'s, covered by `hHome`; the rest are covered by
`hConsTo`. -/
theorem migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_to
    (st : SystemState) (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore)
    (hConsTo : replenishQueueAffinityConsistentOnCore st toCore)
    (hHome : ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid → determineTargetCore st tid = toCore) :
    replenishQueueAffinityConsistentOnCore (migrateSchedContextReplenishment st scId fromCore toCore) toCore := by
  intro scId₀ t hMem sc₀ hSc tid hBound
  rw [migrateSchedContextReplenishment_getSchedContext?] at hSc
  rw [migrateSchedContextReplenishment_determineTargetCore]
  rcases migrateSchedContextReplenishment_mem_toCore st scId fromCore toCore h _ hMem with hOld | ⟨hKey, _⟩
  · exact hConsTo scId₀ t hOld sc₀ hSc tid hBound
  · subst hKey
    exact hHome sc₀ hSc tid hBound

/-- WS-SM SM5.H.4 / SM5.H.5: the migration *preserves* affinity consistency on the
source core `fromCore`, given its entries **other than** `scId`'s are consistent
(`hConsNonScId`).  The post-migration `fromCore` queue is the pre-state queue with
all `scId` entries removed — exactly the non-`scId` entries `hConsNonScId` covers
(the `scId` entries — the only ones the affinity change could have invalidated on
`fromCore` — are gone). -/
theorem migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_from
    (st : SystemState) (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore)
    (hConsNonScId : ∀ (scId₀ : SchedContextId) (t : Nat),
      (scId₀, t) ∈ (st.scheduler.replenishQueueOnCore fromCore).entries → scId₀ ≠ scId →
        ∀ sc₀, st.getSchedContext? scId₀ = some sc₀ →
          ∀ tid, sc₀.boundThread = some tid → determineTargetCore st tid = fromCore) :
    replenishQueueAffinityConsistentOnCore (migrateSchedContextReplenishment st scId fromCore toCore) fromCore := by
  intro scId₀ t hMem sc₀ hSc tid hBound
  rw [migrateSchedContextReplenishment_getSchedContext?] at hSc
  rw [migrateSchedContextReplenishment_determineTargetCore]
  rw [migrateSchedContextReplenishment_replenishQueueOnCore_from st scId fromCore toCore h] at hMem
  have hRem := mem_remove_entries hMem
  exact hConsNonScId scId₀ t hRem.1 hRem.2 sc₀ hSc tid hBound

/-- WS-SM SM5.H.4 / SM5.H.5: the migration *preserves* affinity consistency on any
core `c'` other than `fromCore` / `toCore` — its replenish queue and the object
store are untouched. -/
theorem migrateSchedContextReplenishment_preserves_affinityConsistentOnCore_other
    (st : SystemState) (scId : SchedContextId) (fromCore toCore c' : CoreId)
    (hFrom : fromCore ≠ c') (hTo : toCore ≠ c')
    (hCons : replenishQueueAffinityConsistentOnCore st c') :
    replenishQueueAffinityConsistentOnCore (migrateSchedContextReplenishment st scId fromCore toCore) c' :=
  (replenishQueueAffinityConsistentOnCore_frame
    (migrateSchedContextReplenishment_replenishQueueOnCore_other st scId fromCore toCore c' hFrom hTo)
    (migrateSchedContextReplenishment_objects st scId fromCore toCore)).mpr hCons

/-- WS-RR RR2.3: the migration preserves affinity consistency on **every** core,
given the source core's non-`scId` entries stay put (`hConsFrom`), the
destination's pre-existing entries are consistent (`hConsTo`), the migrated SC is
homed on the destination (`hHome`), and every other core is already consistent
(`hConsOther`).  The whole-state form the live donation arms discharge: the
donation rebinds exactly one SchedContext, so the source is purged of exactly the
entries the rebind invalidated and the destination receives exactly those. -/
theorem migrateSchedContextReplenishment_preserves_affinityConsistent_smp
    (st : SystemState) (scId : SchedContextId) (fromCore toCore : CoreId)
    (hConsOther : ∀ c', fromCore ≠ c' → toCore ≠ c' →
      replenishQueueAffinityConsistentOnCore st c')
    (hConsTo : replenishQueueAffinityConsistentOnCore st toCore)
    (hConsFrom : ∀ (scId₀ : SchedContextId) (t : Nat),
      (scId₀, t) ∈ (st.scheduler.replenishQueueOnCore fromCore).entries → scId₀ ≠ scId →
        ∀ sc₀, st.getSchedContext? scId₀ = some sc₀ →
          ∀ tid, sc₀.boundThread = some tid → determineTargetCore st tid = fromCore)
    (hHome : ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid → determineTargetCore st tid = toCore) :
    replenishQueueAffinityConsistent_smp
      (migrateSchedContextReplenishment st scId fromCore toCore) := by
  intro c
  by_cases hEq : fromCore = toCore
  · -- Self-migration: the identity, and the hypotheses collapse onto `hConsTo`
    -- (source = destination) and `hConsOther` elsewhere.
    subst hEq
    rw [migrateSchedContextReplenishment_noop]
    by_cases hc : fromCore = c
    · subst hc; exact hConsTo
    · exact hConsOther c hc hc
  · by_cases hTo : toCore = c
    · subst hTo
      exact migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_to
        st scId fromCore toCore hEq hConsTo hHome
    · by_cases hFrom : fromCore = c
      · subst hFrom
        exact migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_from
          st scId fromCore toCore hEq hConsFrom
      · exact migrateSchedContextReplenishment_preserves_affinityConsistentOnCore_other
          st scId fromCore toCore c hFrom hTo (hConsOther c hFrom hTo)

end SeLe4n.Kernel
