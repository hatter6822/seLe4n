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


/-- WS-SM SM5.H.5 (frame): the affinity-consistency invariant on core `c` reads
only core `c`'s replenish queue plus the object store (via `getSchedContext?` and
`determineTargetCore`, both pure object-store reads).  A state agreeing on those
agrees on the predicate. -/
theorem replenishQueueAffinityConsistentOnCore_frame {st st' : SystemState} {c : CoreId}
    (hRepl : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (hObj : st'.objectsAgreeOffRunLinks st) :
    replenishQueueAffinityConsistentOnCore st' c ↔
    replenishQueueAffinityConsistentOnCore st c :=
  replenishQueueAffinityConsistentOnCore_congr hRepl
    (fun scId => hObj.getSchedContext? scId)
    (fun tid => determineTargetCore_of_objectsAgreeOffRunLinks hObj tid)

/-- WS-ZA ZA6.3 (frame): ...and across a release-queue write, which holds every
context's bound thread and every thread's home core. -/
theorem replenishQueueAffinityConsistentOnCore_frameRelease {st st' : SystemState} {c : CoreId}
    (hRepl : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (hObj : st'.objectsAgreeOffReleaseLinks st) :
    replenishQueueAffinityConsistentOnCore st' c ↔
    replenishQueueAffinityConsistentOnCore st c := by
  have hB := fun scId => hObj.getSchedContext?_map (·.boundThread) (fun _ => rfl) scId
  have hT : ∀ tid, determineTargetCore st' tid = determineTargetCore st tid := fun tid => by
    unfold determineTargetCore; rw [hObj.getTcb?]
  exact ⟨replenishQueueAffinityConsistentOnCore_transfer st' st c (fun e he => by rw [hRepl]; exact he)
      (fun scId => (hB scId).symm) (fun tid => (hT tid).symm),
   replenishQueueAffinityConsistentOnCore_transfer st st' c (fun e he => by rw [← hRepl]; exact he)
      hB hT⟩

/-- WS-SM SM5.H.5: the SMP form's congruence — the per-core congruence at every
core.  A migration's destination is chosen per state, so a consumer that must
transport the whole-state invariant across a step writing neither replenish
queues nor objects-read-through-`getSchedContext?`/`determineTargetCore` reaches
for this rather than iterating the per-core form by hand. -/
theorem replenishQueueAffinityConsistent_smp_congr {st st' : SystemState}
    (hRepl : ∀ c, st'.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c)
    (hSc : ∀ scId, st'.getSchedContext? scId = st.getSchedContext? scId)
    (hTgt : ∀ tid, determineTargetCore st' tid = determineTargetCore st tid) :
    replenishQueueAffinityConsistent_smp st' ↔ replenishQueueAffinityConsistent_smp st :=
  ⟨fun h c => (replenishQueueAffinityConsistentOnCore_congr (hRepl c) hSc hTgt).mp (h c),
   fun h c => (replenishQueueAffinityConsistentOnCore_congr (hRepl c) hSc hTgt).mpr (h c)⟩

/-- **`v0.35.166`: the SMP form's whole-store frame** — the per-core `_frame` at
every core.

The shape a step that writes *no object at all* and no replenish entry reaches
for: a CDT detach, a service-registry revoke, a memory scrub.  `_smp_congr` would
make each of those re-derive the two object-store readings from the same
`objects` equality, which is what `_frame` exists to do once. -/
theorem replenishQueueAffinityConsistent_smp_frame {st st' : SystemState}
    (hRepl : ∀ c, st'.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c)
    (hObj : st'.objects = st.objects) :
    replenishQueueAffinityConsistent_smp st' ↔ replenishQueueAffinityConsistent_smp st :=
  ⟨fun h c => (replenishQueueAffinityConsistentOnCore_frame (hRepl c) (.of_objects_eq hObj)).mp (h c),
   fun h c => (replenishQueueAffinityConsistentOnCore_frame (hRepl c) (.of_objects_eq hObj)).mpr (h c)⟩

/-- **`v0.35.185` (register row 63): the retype's store preserves the SM5.H
replenish-affinity invariant.**

The other half of `storeObject_establishes_schedContextBindingConsistent`, and it
consumes the **same** readiness predicate — which is the measurement that
`schedContextBindingRetypeReady` is the intermediate the destroy path needs
rather than one invariant's private scaffolding.

Three readings, and the carve-outs answer the two the store can move.  The
entries are the pre-state's (`storeObject` writes no scheduler state).  A context
**at** `target` is the replacement's, whose `boundThread` is `none` — a runtime
refusal since `v0.35.184` — so it constrains nothing; a context elsewhere is the
pre-state's.  And the thread such a context names is not at `target`
(readiness's backward clause), so its `cpuAffinity` — the only field
`determineTargetCore` reads — survives the store untouched.

Without the carve-out the last step is *false*: the replacement TCB's affinity is
its own, so a surviving context still naming the destroyed thread would have its
entries on whatever core the replacement happens to declare. -/
theorem storeObject_preserves_replenishQueueAffinityConsistent_smp
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hObjInv : st.objects.invExt)
    (hScFresh : ∀ sc : SchedContext, newObj = .schedContext sc → sc.boundThread = none)
    (hReady : schedContextBindingRetypeReady st target)
    (hStore : storeObject target newObj st = .ok ((), st'))
    (h : replenishQueueAffinityConsistent_smp st) :
    replenishQueueAffinityConsistent_smp st' := by
  have hAt : st'.objects[target]? = some newObj :=
    storeObject_objects_eq st st' target newObj hObjInv hStore
  have hOff : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]? :=
    fun oid hNe => storeObject_objects_ne st st' target oid newObj hNe hObjInv hStore
  have hSched : st'.scheduler = st.scheduler :=
    storeObject_scheduler_eq st st' target newObj hStore
  intro c scId t hMem sc hSc tid hBT
  rw [hSched] at hMem
  have hScRaw : st'.objects[scId.toObjId]? = some (.schedContext sc) :=
    (SystemState.getSchedContext?_eq_some_iff st' scId sc).mp hSc
  by_cases hTgt : scId.toObjId = target
  · -- The replacement's own context binds nobody, so it constrains no entry.
    rw [hTgt, hAt] at hScRaw
    cases newObj with
    | schedContext s0 =>
      have hSame : s0 = sc := by injection Option.some.inj hScRaw
      rw [← hSame, hScFresh s0 rfl] at hBT
      exact absurd hBT (by simp)
    | _ => exact absurd hScRaw (by simp)
  · rw [hOff _ hTgt] at hScRaw
    obtain ⟨hTidNe, _⟩ := hReady.2 scId sc hScRaw hTgt tid hBT
    -- The bound thread is not the destroyed key, so its home core is unmoved.
    have hTcbEq : st'.getTcb? tid = st.getTcb? tid := by
      unfold SystemState.getTcb?; rw [hOff _ hTidNe]
    rw [show determineTargetCore st' tid = determineTargetCore st tid from by
      unfold determineTargetCore; rw [hTcbEq]]
    exact h c scId t hMem sc
      ((SystemState.getSchedContext?_eq_some_iff st scId sc).mpr hScRaw) tid hBT

/-- **WS-RR RR8.11: the core a scheduling context's replenishments must sit on.**

This is `replenishQueueAffinityConsistentOnCore`'s own reading, made a function:
the invariant demands of every entry naming `scId` that the home of `scId`'s
**bound thread** be the entry's core, so that home *is* the destination any
migration of `scId` must aim at.  `fallback` answers the two shapes on which the
invariant constrains nothing — the context resolving to no object, and a context
bound to no thread — where the antecedent `sc.boundThread = some tid` is
unsatisfiable, so no entry can distinguish the choices.

**Why a migration reads this rather than the thread it expects to rebind to.**
A caller that knows which thread it is *about* to bind `scId` to can pass that
thread's home, and that is right exactly when the rebind commits.  Where the
rebinding step can refuse — the cancellation reclaim, whose guards are fail-closed
(WS-RR RR8.11) — the expected thread is a **proxy** for the bound thread and the
proxy is wrong on precisely the refused states: the migration then moves entries
to a core no thread bound to `scId` is homed on, which is the invariant's own
negation.  Reading the fact instead makes the refused case a *self*-migration,
which `migrateSchedContextReplenishment_noop` collapses to the identity, and makes
the destination obligation (`hHome` of
`migrateSchedContextReplenishment_preserves_affinityConsistent_smp`) free.

Every caller passes the migration's **source** core as `fallback`, so the two
unconstrained shapes are no-ops too rather than pointless moves. -/
def replenishHomeOfSchedContext (st : SystemState) (scId : SchedContextId)
    (fallback : CoreId) : CoreId :=
  match st.getSchedContext? scId with
  | none => fallback
  | some sc =>
    match sc.boundThread with
    | none => fallback
    | some tid => determineTargetCore st tid

/-- WS-RR RR8.11: **the destination obligation, discharged by construction.**
This is literally `migrateSchedContextReplenishment_preserves_affinityConsistent_smp`'s
`hHome` at `toCore := replenishHomeOfSchedContext st scId fallback`, and it takes
no hypothesis — which is the whole point of resolving the destination from the
bound thread rather than from the thread a caller expects to bind. -/
theorem replenishHomeOfSchedContext_spec (st : SystemState) (scId : SchedContextId)
    (fallback : CoreId) :
    ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid →
        determineTargetCore st tid = replenishHomeOfSchedContext st scId fallback := by
  intro sc hSc tid hBound
  simp only [replenishHomeOfSchedContext, hSc, hBound]

/-- WS-RR RR8.11: the destination at a context bound to a thread. -/
theorem replenishHomeOfSchedContext_eq_of_bound (st : SystemState)
    (scId : SchedContextId) (fallback : CoreId) (sc : SeLe4n.Kernel.SchedContext)
    (tid : SeLe4n.ThreadId) (hSc : st.getSchedContext? scId = some sc)
    (hBound : sc.boundThread = some tid) :
    replenishHomeOfSchedContext st scId fallback = determineTargetCore st tid :=
  (replenishHomeOfSchedContext_spec st scId fallback sc hSc tid hBound).symm

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
-- `Scheduler/Operations/Core.lean`) unlinks `scId` from `fromCore`'s release
-- queue and links it into `toCore`'s at the release time its link held, and is a
-- no-op when the two cores coincide.  It writes the two release-queue slots and
-- the contexts' release fields alone: every run queue, every current slot, every
-- other per-core slot and every object off its release fields are untouched, so
-- `getSchedContext?` (off the release fields) and `determineTargetCore` read
-- through it.

/-- WS-SM SM5.H.4: a self-migration (`fromCore = toCore`) is the identity. -/
@[simp] theorem migrateSchedContextReplenishment_noop (st : SystemState)
    (scId : SchedContextId) (c : CoreId) :
    migrateSchedContextReplenishment st scId c c = st := by
  unfold migrateSchedContextReplenishment; rw [if_pos rfl]

/-- The migration's link step: the context's link moved when the source's links
queue it, the state otherwise. -/
private theorem migrate_linkStep_releaseOnlyWrite (st : SystemState) (scId : SchedContextId)
    (fromCore toCore : CoreId) :
    (if st.releaseQueuedOn fromCore scId then
        (st.releaseRemoveOn fromCore scId).releaseInsertOn toCore scId (st.releaseAtOn fromCore scId)
      else st).releaseOnlyWrite st := by
  split
  · exact (SystemState.releaseInsertOn_releaseOnlyWrite _ _ _ _).trans
      (SystemState.releaseRemoveOn_releaseOnlyWrite _ _ _)
  · exact .refl _

private theorem migrate_linkStep_agree (st : SystemState) (scId : SchedContextId)
    (fromCore toCore : CoreId) :
    (if st.releaseQueuedOn fromCore scId then
        (st.releaseRemoveOn fromCore scId).releaseInsertOn toCore scId (st.releaseAtOn fromCore scId)
      else st).objectsAgreeOffReleaseLinks st := by
  split
  · exact (SystemState.releaseInsertOn_agree _ _ _ _).trans (SystemState.releaseRemoveOn_agree _ _ _)
  · exact .refl _

private theorem migrate_linkStep_objects_invExt (st : SystemState) (scId : SchedContextId)
    (fromCore toCore : CoreId) (h : st.objects.invExt) :
    (if st.releaseQueuedOn fromCore scId then
        (st.releaseRemoveOn fromCore scId).releaseInsertOn toCore scId (st.releaseAtOn fromCore scId)
      else st).objects.invExt := by
  split
  · exact SystemState.releaseInsertOn_objects_invExt _ _ _ _
      (SystemState.releaseRemoveOn_objects_invExt _ _ _ h)
  · exact h

/-- WS-ZA ZA6.3: the migration writes the release queues and the contexts'
release fields alone. -/
theorem migrateSchedContextReplenishment_releaseOnlyWrite (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).releaseOnlyWrite st := by
  unfold migrateSchedContextReplenishment
  split
  · exact .refl _
  · exact (migrate_linkStep_releaseOnlyWrite st scId fromCore toCore).withScheduler
      (SchedulerState.releaseOnly.setReplenishQueueOnCore
        (SchedulerState.releaseOnly.setReplenishQueueOnCore (.refl _) _ _) _ _)

/-- WS-ZA ZA6.3: the migration holds every object off the release links. -/
theorem migrateSchedContextReplenishment_agree (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).objectsAgreeOffReleaseLinks st := by
  unfold migrateSchedContextReplenishment
  split
  · exact .refl _
  · exact (migrate_linkStep_agree st scId fromCore toCore).withScheduler _

/-- The migration keeps the object table's extension invariant. -/
theorem migrateSchedContextReplenishment_preserves_objects_invExt (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : st.objects.invExt) :
    (migrateSchedContextReplenishment st scId fromCore toCore).objects.invExt := by
  unfold migrateSchedContextReplenishment
  split
  · exact h
  · exact migrate_linkStep_objects_invExt st scId fromCore toCore h

/-- ...and the derivation tree itself (`v0.35.199`). -/
@[simp] theorem migrateSchedContextReplenishment_cdt (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).cdt = st.cdt := by
  rw [(migrateSchedContextReplenishment_releaseOnlyWrite st scId fromCore toCore).1]

/-- WS-SM SM5.H.4: the migration never advances the machine timer. -/
@[simp] theorem migrateSchedContextReplenishment_machine (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).machine = st.machine :=
  (migrateSchedContextReplenishment_releaseOnlyWrite st scId fromCore toCore).machine

/-- `v0.35.164`: the migration never touches the TLB-shootdown state either. -/
@[simp] theorem migrateSchedContextReplenishment_tlbShootdown (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).tlbShootdown
      = st.tlbShootdown := by
  rw [(migrateSchedContextReplenishment_releaseOnlyWrite st scId fromCore toCore).1]

/-- WS-SM SM5.H.4 (frame): the replenishment migration leaves **every** run-queue
slot untouched. -/
@[simp] theorem migrateSchedContextReplenishment_runQueueOnCore (st : SystemState)
    (scId : SchedContextId) (fromCore toCore c' : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
  rw [(migrateSchedContextReplenishment_releaseOnlyWrite st scId fromCore toCore).2]; rfl

/-- WS-SM SM5.H.4: the migration frames every SchedContext resolution off its
release-queue fields. -/
theorem migrateSchedContextReplenishment_getSchedContext? (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (scId' : SchedContextId) :
    ((migrateSchedContextReplenishment st scId fromCore toCore).getSchedContext? scId').map
        SchedContext.withoutRelease
      = (st.getSchedContext? scId').map SchedContext.withoutRelease :=
  (migrateSchedContextReplenishment_agree st scId fromCore toCore).getSchedContext? scId'

/-- ...so every context's bound thread reads the same. -/
theorem migrateSchedContextReplenishment_boundThread (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (scId' : SchedContextId) :
    ((migrateSchedContextReplenishment st scId fromCore toCore).getSchedContext? scId').map
        (·.boundThread)
      = (st.getSchedContext? scId').map (·.boundThread) :=
  (migrateSchedContextReplenishment_agree st scId fromCore toCore).getSchedContext?_map _
    (fun _ => rfl) scId'

/-- WS-SM SM5.H.4: the migration frames every thread's TCB resolution. -/
theorem migrateSchedContextReplenishment_getTcb? (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (tid : SeLe4n.ThreadId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).getTcb? tid
      = st.getTcb? tid :=
  (migrateSchedContextReplenishment_agree st scId fromCore toCore).getTcb? tid

/-- WS-SM SM5.H.4: the migration frames every thread's home core. -/
theorem migrateSchedContextReplenishment_determineTargetCore (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (tid : SeLe4n.ThreadId) :
    determineTargetCore (migrateSchedContextReplenishment st scId fromCore toCore) tid
      = determineTargetCore st tid := by
  unfold determineTargetCore; rw [migrateSchedContextReplenishment_getTcb?]

/-- WS-SM SM5.H.4 / SM6.E: the migration never disturbs any core's run queue or
current slot. -/
theorem migrateSchedContextReplenishment_runQueue_current_eq (st : SystemState)
    (scId : SchedContextId) (fromCore toCore c : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.runQueueOnCore c
        = st.scheduler.runQueueOnCore c
    ∧ (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.currentOnCore c
        = st.scheduler.currentOnCore c := by
  rw [(migrateSchedContextReplenishment_releaseOnlyWrite st scId fromCore toCore).2]
  exact ⟨rfl, rfl⟩

/-- WS-SM SM5.H.4: core `toCore`'s post-migration abstract queue is its pre-state
queue with `scId`'s source entries inserted, each at its own time
(`fromCore ≠ toCore`). -/
theorem migrateSchedContextReplenishment_replenishQueueOnCore_to (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore toCore
      = ((st.scheduler.replenishQueueOnCore fromCore).entries.filter (fun e => e.1 == scId)).foldl
          (fun q e => q.insert scId e.2) (st.scheduler.replenishQueueOnCore toCore) := by
  unfold migrateSchedContextReplenishment; rw [if_neg h]
  exact SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self _ _ _

/-- WS-SM SM5.H.4: core `fromCore`'s post-migration abstract queue is its
pre-state queue with `scId`'s entry removed (`fromCore ≠ toCore`). -/
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
  split
  · rfl
  · dsimp only
    rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hTo,
      SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hFrom]
    split
    · rw [SystemState.releaseInsertOn_replenishQueueOnCore_ne _ _ _ _ _ (Ne.symm hTo),
        SystemState.releaseRemoveOn_replenishQueueOnCore, if_neg (Ne.symm hFrom)]
    · rfl

/-- An entry list whose keys are distinct holds `s`'s one entry alone among
those naming `s`. -/
private theorem filter_key_eq_singleton {s : SchedContextId} {t : Nat} :
    ∀ {l : List (SchedContextId × Nat)}, (l.map Prod.fst).Nodup → (s, t) ∈ l →
      l.filter (fun e => e.1 == s) = [(s, t)]
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, hn, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with e | hm
    · subst e
      rw [List.filter_cons, if_pos (by simp), List.filter_eq_nil_iff.mpr]
      intro x hx hk
      exact hn.1 (List.mem_map.mpr ⟨x, hx, by simpa using hk⟩)
    · have ha : (a.1 == s) = false := by
        rw [beq_eq_false_iff_ne]; intro e
        exact hn.1 (e ▸ List.mem_map.mpr ⟨_, hm, rfl⟩)
      rw [List.filter_cons, if_neg (by simp [ha]), filter_key_eq_singleton hn.2 hm]

/-- WS-ZA ZA6.3: **the migration keeps the release queues refined.**  Its link
step is a removal and an insert, each refined; the abstract queues it then
writes are the ones the link step already holds — `fromCore`'s without the
context, `toCore`'s with the one entry the context's link keyed. -/
theorem migrateSchedContextReplenishment_refined {st : SystemState}
    (h : st.releaseQueueRefined) (scId : SchedContextId) (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).releaseQueueRefined := by
  by_cases hft : fromCore = toCore
  · subst hft; rw [migrateSchedContextReplenishment_noop]; exact h
  have hFrom := h fromCore
  let st₁ := if st.releaseQueuedOn fromCore scId then
      (st.releaseRemoveOn fromCore scId).releaseInsertOn toCore scId (st.releaseAtOn fromCore scId)
    else st
  have h₁ : st₁.releaseQueueRefined := by
    show SystemState.releaseQueueRefined (if _ then _ else _)
    split
    · exact SystemState.releaseInsertOn_refined (SystemState.releaseRemoveOn_refined h _ _) _ _ _
    · exact h
  unfold migrateSchedContextReplenishment; rw [if_neg hft]; dsimp only
  refine SystemState.releaseQueueRefined_of_entries (st := st₁) (fun _ _ => rfl) (fun c => ?_)
    rfl rfl h₁
  by_cases hcT : c = toCore
  · subst hcT
    rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self]
    show _ = (((if _ then _ else _) : SystemState).scheduler.replenishQueueOnCore c).entries
    split
    · rename_i hq
      rw [filter_key_eq_singleton hFrom.nodup (hFrom.mem_of_queued hq), List.foldl_cons,
        List.foldl_nil]
      have hfree := SystemState.releaseRemoveOn_not_queued hq
      have hsome : ((st.releaseRemoveOn fromCore scId).getSchedContext? scId).isSome = true := by
        rw [(SystemState.releaseRemoveOn_agree st fromCore scId).getSchedContext?_isSome]
        unfold SystemState.releaseQueuedOn at hq
        cases e : st.getSchedContext? scId <;> rw [e] at hq
        · cases hq
        · rfl
      rw [SystemState.releaseInsertOn_eq_fresh hfree hsome,
        SystemState.releaseInsertFresh_replenishQueueOnCore, if_pos rfl,
        SystemState.releaseRemoveOn_replenishQueueOnCore, if_neg (Ne.symm hft)]
    · rename_i hq
      have hn : (st.scheduler.replenishQueueOnCore fromCore).entries.filter
          (fun e => e.1 == scId) = [] := by
        rw [List.filter_eq_nil_iff]; intro e he hk
        have hk' : e.1 = scId := by simpa using hk
        exact hFrom.not_mem_of_not_queued (by simpa using hq) e.2
          (by obtain ⟨a, b⟩ := e; dsimp only at hk' ⊢; subst hk'; exact he)
      rw [hn]; rfl
  · rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ (Ne.symm hcT)]
    by_cases hcF : c = fromCore
    · subst hcF
      rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self]
      show _ = (((if _ then _ else _) : SystemState).scheduler.replenishQueueOnCore c).entries
      split
      · rw [SystemState.releaseInsertOn_replenishQueueOnCore_ne _ _ _ _ _ hcT,
          SystemState.releaseRemoveOn_replenishQueueOnCore, if_pos rfl]
      · rename_i hq
        show List.filter _ _ = _
        rw [List.filter_eq_self]; intro e he
        have : e.1 ≠ scId := fun hk =>
          hFrom.not_mem_of_not_queued (by simpa using hq) e.2
            (by obtain ⟨a, b⟩ := e; dsimp only at hk ⊢; subst hk; exact he)
        simp [this]
    · rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ (Ne.symm hcF)]

-- ============================================================================
-- §4  SM5.H.4 — the migration genuinely *moves* the SchedContext's entries
-- ============================================================================

/-- WS-SM SM5.H.4: after a migration (`fromCore ≠ toCore`), **no** `scId`
replenishment remains in `fromCore`'s queue. -/
theorem migrateSchedContextReplenishment_fromCore_excludes_scId (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore) (t : Nat) :
    (scId, t) ∉ ((migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore fromCore).entries := by
  rw [migrateSchedContextReplenishment_replenishQueueOnCore_from st scId fromCore toCore h]
  intro hMem
  exact (mem_remove_entries hMem).2 rfl

/-- WS-SM SM5.H.4: every entry in `toCore`'s post-migration queue either was
already there, or is one of `scId`'s entries `fromCore`'s queue held. -/
theorem migrateSchedContextReplenishment_mem_toCore (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore)
    (e : SchedContextId × Nat)
    (hMem : e ∈ ((migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore toCore).entries) :
    e ∈ (st.scheduler.replenishQueueOnCore toCore).entries ∨
      (e.1 = scId ∧ e ∈ (st.scheduler.replenishQueueOnCore fromCore).entries) := by
  rw [migrateSchedContextReplenishment_replenishQueueOnCore_to st scId fromCore toCore h] at hMem
  rcases mem_foldl_insert_provenance _ scId _ _ hMem with hOld | ⟨x, hx, hEq⟩
  · exact Or.inl hOld
  · obtain ⟨hxMem, hxK⟩ := List.mem_filter.mp hx
    have hK : x.1 = scId := by simpa [beq_iff_eq] using hxK
    subst hEq
    exact Or.inr ⟨rfl, by rw [← hK]; exact hxMem⟩

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
  obtain ⟨sc₁, hSc₁, e⟩ :=
    (migrateSchedContextReplenishment_agree st scId fromCore toCore).getSchedContext?_some' hSc
  have hB : sc₁.boundThread = some tid := by
    rw [← hBound]; exact (congrArg (·.boundThread) e).symm
  rw [migrateSchedContextReplenishment_determineTargetCore]
  rcases migrateSchedContextReplenishment_mem_toCore st scId fromCore toCore h _ hMem with hOld | ⟨hKey, _⟩
  · exact hConsTo scId₀ t hOld sc₁ hSc₁ tid hB
  · subst hKey
    exact hHome sc₁ hSc₁ tid hB

/-- WS-SM SM5.H.4 / SM5.H.5: the migration *preserves* affinity consistency on the
source core `fromCore`, given its entries **other than** `scId`'s are consistent
(`hConsNonScId`).  The post-migration `fromCore` queue is the pre-state queue with
all `scId` entries removed — exactly the non-`scId` entries `hConsNonScId` covers
(the `scId` entries — the only ones the affinity change could have invalidated on
`fromCore` — are gone). -/
theorem migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_from
    (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore)
    (hConsNonScId : ∀ (scId₀ : SchedContextId) (t : Nat),
      (scId₀, t) ∈ (st.scheduler.replenishQueueOnCore fromCore).entries → scId₀ ≠ scId →
        ∀ sc₀, st.getSchedContext? scId₀ = some sc₀ →
          ∀ tid, sc₀.boundThread = some tid → determineTargetCore st tid = fromCore) :
    replenishQueueAffinityConsistentOnCore (migrateSchedContextReplenishment st scId fromCore toCore) fromCore := by
  intro scId₀ t hMem sc₀ hSc tid hBound
  obtain ⟨sc₁, hSc₁, e⟩ :=
    (migrateSchedContextReplenishment_agree st scId fromCore toCore).getSchedContext?_some' hSc
  have hB : sc₁.boundThread = some tid := by
    rw [← hBound]; exact (congrArg (·.boundThread) e).symm
  rw [migrateSchedContextReplenishment_determineTargetCore]
  rw [migrateSchedContextReplenishment_replenishQueueOnCore_from st scId fromCore toCore h] at hMem
  have hRem := mem_remove_entries hMem
  exact hConsNonScId scId₀ t hRem.1 hRem.2 sc₁ hSc₁ tid hB

/-- WS-SM SM5.H.4 / SM5.H.5: the migration *preserves* affinity consistency on any
core `c'` other than `fromCore` / `toCore` — its replenish queue and the object
store are untouched. -/
theorem migrateSchedContextReplenishment_preserves_affinityConsistentOnCore_other
    (st : SystemState) (scId : SchedContextId) (fromCore toCore c' : CoreId)
    (hFrom : fromCore ≠ c') (hTo : toCore ≠ c')
    (hCons : replenishQueueAffinityConsistentOnCore st c') :
    replenishQueueAffinityConsistentOnCore (migrateSchedContextReplenishment st scId fromCore toCore) c' :=
  (replenishQueueAffinityConsistentOnCore_frameRelease
    (migrateSchedContextReplenishment_replenishQueueOnCore_other st scId fromCore toCore c' hFrom hTo)
    (migrateSchedContextReplenishment_agree st scId fromCore toCore)).mpr hCons

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

/-- **WS-RR RR8.11: migrating a rebound scheduling context to its own new home
restores affinity consistency on every core.**

The general form of what every rebinding-then-migrating transition owes, stated so
the *destination* is `replenishHomeOfSchedContext` of the post-rebind state rather
than a core the caller expects the rebind to produce.  Four things the rebinding
step must supply, and none of them is "the rebind succeeded": that it wrote no
replenish queue (`hRepl`), that it wrote no *other* scheduling context
(`hOther`), that it moved no thread's home core (`hTgt`), and that the migration's
**source** is where the invariant currently puts this context — spelled as the
pre-state binding and its home (`hSrcGet` / `hSrcBound` / `hSrcHome`) rather than
as an implication, because a context that resolves to nothing or is bound to no
thread constrains no entry and so cannot locate the entries a migration would
move.

`hHome`, the obligation that the destination is right, is
`replenishHomeOfSchedContext_spec` and costs nothing. -/
theorem migrateSchedContextReplenishment_to_home_preserves_affinityConsistent_smp
    (st st' : SystemState) (scId : SchedContextId) (fromCore : CoreId)
    (srcSc : SeLe4n.Kernel.SchedContext) (srcTid : SeLe4n.ThreadId)
    (hRepl : ∀ c, st'.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c)
    (hOther : ∀ scId₀, scId₀ ≠ scId → st'.getSchedContext? scId₀ = st.getSchedContext? scId₀)
    (hTgt : ∀ tid, determineTargetCore st' tid = determineTargetCore st tid)
    (hSrcGet : st.getSchedContext? scId = some srcSc)
    (hSrcBound : srcSc.boundThread = some srcTid)
    (hSrcHome : determineTargetCore st srcTid = fromCore)
    (hCons : replenishQueueAffinityConsistent_smp st) :
    replenishQueueAffinityConsistent_smp
      (migrateSchedContextReplenishment st' scId fromCore
        (replenishHomeOfSchedContext st' scId fromCore)) := by
  have hOtherCons : ∀ (c : CoreId) (scId₀ : SchedContextId) (t : Nat),
      (scId₀, t) ∈ (st'.scheduler.replenishQueueOnCore c).entries → scId₀ ≠ scId →
        ∀ sc₀, st'.getSchedContext? scId₀ = some sc₀ →
          ∀ tid, sc₀.boundThread = some tid → determineTargetCore st' tid = c := by
    intro c scId₀ t hMem hne sc₀ hSc₀ tid hB
    rw [hRepl c] at hMem
    rw [hOther scId₀ hne] at hSc₀
    rw [hTgt tid]
    exact hCons c scId₀ t hMem sc₀ hSc₀ tid hB
  have hConfined : ∀ (c : CoreId) (t : Nat),
      (scId, t) ∈ (st'.scheduler.replenishQueueOnCore c).entries → c = fromCore := by
    intro c t hMem
    rw [hRepl c] at hMem
    rw [← hSrcHome]
    exact (hCons c scId t hMem srcSc hSrcGet srcTid hSrcBound).symm
  refine migrateSchedContextReplenishment_preserves_affinityConsistent_smp st' scId fromCore _
    (fun c' hFrom _ => ?_) ?_ (fun scId₀ t hMem hne sc₀ hSc₀ tid hB =>
      hOtherCons fromCore scId₀ t hMem hne sc₀ hSc₀ tid hB)
    (replenishHomeOfSchedContext_spec st' scId fromCore)
  · intro scId₀ t hMem sc₀ hSc₀ tid hB
    by_cases hk : scId₀ = scId
    · subst hk; exact absurd (hConfined c' t hMem) (fun hc => hFrom hc.symm)
    · exact hOtherCons c' scId₀ t hMem hk sc₀ hSc₀ tid hB
  · intro scId₀ t hMem sc₀ hSc₀ tid hB
    by_cases hk : scId₀ = scId
    · rw [hk] at hSc₀
      exact replenishHomeOfSchedContext_spec st' scId fromCore sc₀ hSc₀ tid hB
    · exact hOtherCons _ scId₀ t hMem hk sc₀ hSc₀ tid hB

end SeLe4n.Kernel
