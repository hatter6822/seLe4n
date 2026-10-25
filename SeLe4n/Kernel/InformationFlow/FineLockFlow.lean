-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM8.D — information flow under fine locks
-- (WS-SM SM8.D.1 … SM8.D.6).

import SeLe4n.Kernel.InformationFlow.CovertChannelPerCore
import SeLe4n.Kernel.Concurrency.Locks.LockSetForSyscall
import SeLe4n.Kernel.Concurrency.Locks.BracketSpec

/-!
# WS-SM SM8.D — information flow under fine locks

WS-SM SM8 §5 sub-tasks SM8.D.1 …
SM8.D.5 (SM8.D.6 is the scenario suite in `tests/SmpInformationFlowSuite.lean`).

SM8.A built the per-core observer, SM8.B proved what the SMP kernel does not
leak and registered what it does, SM8.C audited the one flow it deliberately
permits.  This module is about the **lock state itself**: the `RwLockState`
the SM3 two-phase-locking bracket advances on every acquire and every release.
Since WS-LS LS3.1 that state is the ghost lock table
(`Concurrency/Locks/LockState.lean`) carried beside the kernel state in a
`LockedSystemState`, not a word inside any kernel object.

## What the plan's table said, and what became of it

The SM8.D table was written while `projectKernelObject` carried each object's
`lock` into the observable state.  SM8.B.4 erased it from the projection — three
fields of `CoreId`s on every object kind re-opened the SM5.B placement channel —
and WS-LS LS3.1 deleted the fields, moving the lock state into the ghost table.
That moves D.1 … D.3 rather than discharging them:

* **D.1** is no longer "document what an observer sees of the lock"; it is the
  statement that an observer sees *nothing* of it, and a statement is a
  theorem, not a docstring.  §1 proves it in the strongest available form: the
  observer's view of a locked state is a function of its kernel half, so no
  part of any observer's view on any core is a function of the lock table.
* **D.2** is then an instance: reader multiplicity is one coordinate of a
  table entry (§2), and what is left of it is the CC-5 *timing* claim.
* **D.3** is **false as written** at the model level — a blocked reader sees
  nothing of writer exclusion in the projection — and §3 states the true form:
  what a blocked acquirer observes is *delay*, that delay is CC-5, and under the
  SM2.C fairness assumption it is **bounded**, so the channel has a bounded
  per-acquisition alphabet exactly as CC-1 does.  The bound is denominated in
  **lock operations**, not seconds — `lockContention_wallClock_bounded` is the
  timing statement, and it carries the per-critical-section ceiling that
  conversion needs as an explicit hypothesis.
* **D.4** (§4) is simplified rather than moved: an acquire writes no object,
  so integrity is stated over raw stored objects.  **D.5** (§5) is about the
  live path's bracket, which runs over the pair.

## Section map

* §1 (SM8.D.1) — `setLockAt`, an arbitrary table write; `lockWritesOnly`,
  the state-level "this step moved nothing but the lock table"; its
  invisibility on every core; and the bracket instance.
* §2 (SM8.D.2) — reader multiplicity is not observable, instantiated at the
  SM2.C reachable multi-reader witness; and the CC-5 restatement.
* §3 (SM8.D.3) — writer exclusion is not observable either; the blocked
  acquirer's observation is its admission delay; the delay bound, the
  alphabet bound and the trace-capacity bound.
* §4 (SM8.D.4) — Biba integrity under per-core locks, in **both** integrity
  directions, with the two theorems that stop it being vacuous.
* §5 (SM8.D.5) — the secure-information-flow witness for a 2PL-bracketed live
  syscall entry, including the sharpened fail-closed statement.

## Which runtime lock §3's bound is about (WS-RR RR6.10)

§3's contention bound is denominated in **lock operations** and rests on the
SM2.C fairness assumption over `RwLockExecution`, i.e. over the *abstract*
`RwLockState` and its strict-FIFO `applyOp`.  For that to bound a channel in
the kernel that runs, the lock the kernel deploys has to be the one the spec
describes.

Through v0.34.48 it was not.  `lock_bridge.rs`'s `STATIC_RW_LOCK_POOL` held
`rw_lock::RwLock`, the CAS-retry implementation, whose refinement relation
(`rwLockSim`) represents no queue at all: a reader arriving while a writer is
queued may be admitted ahead of it, so a contending core's admission delay is
not bounded by its position in any queue and §3's alphabet bound described a
lock nothing ran.

WS-RR RR6.10 points the pool at `queued_rw_lock::QueuedRwLock`, the ticket
FIFO lock, whose refinement
(`Concurrency/Locks/QueuedRwLockRefinement.lean`) relates the abstract
`waiters` queue to the half-open ticket interval `[now_serving, next_ticket)`
**in order**, so admission order is the spec's queue order as a theorem
(`queuedRwLock_admits_in_spec_order`).  §3's bound is therefore about the
deployed primitive.

Axiom-clean: every declaration depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`), checked exhaustively
by `scripts/check_module_axioms.py`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId numCores RwLockState RwLockOp AccessMode LockId
  LockSet LockKey LockState LockedSystemState)

-- ============================================================================
-- §1  SM8.D.1 — the observer sees nothing of the lock
-- ============================================================================
--
-- The SM8.B.4 result is that the 2PL bracket does not move the projection.
-- That is a statement about the *operations* the bracket performs.  D.1 asks
-- the stronger question — what can an observer learn about the lock state at
-- all? — and since WS-LS LS3.1 the answer is nothing **by type**: the lock
-- state is the ghost table `LockedSystemState.locks`, every projection takes a
-- `SystemState`, and a locked state is observed through its `kernel` half
-- alone.  There is no lock word inside the kernel state for a projection to
-- erase, so no erasure argument is needed; the theorems below state the
-- consequence at the forms D.1 … D.4 quantify over.

/-- SM8.D.1: **writing an arbitrary word into the ghost lock table** at key `k`
— free, write-held by any core, read-held by any set of cores, with any queue
of waiters.  The form D.1, D.2 and D.3 quantify over. -/
def setLockAt (s : LockedSystemState) (k : LockKey) (l : RwLockState) : LockedSystemState :=
  { s with locks := s.locks.update k (fun _ => l) }

/-- SM8.D.1: **the state-level relation** — this step wrote nothing but the
lock table.  Over the pair that is literal kernel-half equality: the bracket's
growing and shrinking phases leave `kernel` untouched and advance `locks`. -/
def lockWritesOnly (s s' : LockedSystemState) : Prop :=
  s'.kernel = s.kernel

theorem lockWritesOnly_refl (s : LockedSystemState) : lockWritesOnly s s := rfl

theorem lockWritesOnly_trans {s₁ s₂ s₃ : LockedSystemState}
    (h₁ : lockWritesOnly s₁ s₂) (h₂ : lockWritesOnly s₂ s₃) : lockWritesOnly s₁ s₃ :=
  h₂.trans h₁

/-- SM8.D.1: any rewrite of the lock table is a lock-only step — the growing
phase (`LockState.acquireAll`), the shrinking phase (`LockState.unwindAll`), a
single acquire, release or withdrawal, all at once. -/
theorem lockTableWrite_lockWritesOnly (s : LockedSystemState) (f : LockState → LockState) :
    lockWritesOnly s { s with locks := f s.locks } := rfl

theorem setLockAt_lockWritesOnly (s : LockedSystemState) (k : LockKey) (l : RwLockState) :
    lockWritesOnly s (setLockAt s k l) := rfl

/-- SM8.D.1 (**the D.1 headline at the state level**): a lock-only step is
invisible to the single-core observer. -/
theorem lockWritesOnly_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    {s s' : LockedSystemState} (h : lockWritesOnly s s') :
    projectState ctx observer s'.kernel = projectState ctx observer s.kernel := by
  rw [h]

/-- SM8.D.1 (**the D.1 headline, per core**): and to the observer `(c, L)` on
*every* core. -/
theorem lockWritesOnly_preserves_onCore (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    {s s' : LockedSystemState} (h : lockWritesOnly s s') :
    ObservableState.onCore ctx c L s'.kernel = ObservableState.onCore ctx c L s.kernel := by
  rw [h]

/-- SM8.D.1: the same at an arbitrary `IfObserver`, the form the SM8.B
non-interference surface is stated over. -/
theorem lockWritesOnly_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (c : CoreId) {s s' : LockedSystemState} (h : lockWritesOnly s s') :
    projectStateOnCore ctx observer s'.kernel c = projectStateOnCore ctx observer s.kernel c := by
  rw [h]

/-- SM8.D.1: the `lowEquivalent_smp` form, for composition with the SM8.B
surface. -/
theorem lockWritesOnly_lowEquivalent_smp (ctx : LabelingContext) (observer : IfObserver)
    {s s' : LockedSystemState} (h : lockWritesOnly s s') :
    lowEquivalent_smp ctx observer s'.kernel s.kernel := fun _ => by rw [h]; rfl

/-- SM8.D.1: a **decidable refuter** for `lockWritesOnly`.

Not an `iff`: kernel-state equality is not decidable (`KernelObject` has no
`DecidableEq` — WS-G5 removed it because `RHTable`'s structural equality would
hide hash-layout non-determinism).  What *is* decidable is the object index and
the per-object *kind*, and a step that moved either moved the kernel state.  So
a `false` here is a genuine refutation, which is what a test needs; a `true` is
necessary and not sufficient (`lockWritesOnly_lockWritesOnlyCheck`). -/
def lockWritesOnlyCheck (s s' : LockedSystemState) : Bool :=
  (s'.kernel.objectIndex == s.kernel.objectIndex) &&
    s.kernel.objectIndex.all (fun oid =>
      (s'.kernel.getObjectType? oid) == (s.kernel.getObjectType? oid))

/-- SM8.D.1: the refuter is **sound** — a lock-only step passes it. -/
theorem lockWritesOnly_lockWritesOnlyCheck {s s' : LockedSystemState} (h : lockWritesOnly s s') :
    lockWritesOnlyCheck s s' = true := by
  unfold lockWritesOnlyCheck
  rw [h]
  simp

/-- SM8.D.1 (**the direct form of D.1**): *whatever* the table says at a key,
the observer `(c, L)` sees exactly the same state on every core. -/
theorem onCore_lock_invisible (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : LockedSystemState) (k : LockKey) (l : RwLockState) :
    ObservableState.onCore ctx c L (setLockAt s k l).kernel
      = ObservableState.onCore ctx c L s.kernel := rfl

/-- SM8.D.1: and no observer can distinguish *two* lock words either — the
version with no reference to a "starting" lock state, which is what makes it a
statement about the lock state rather than about a particular write. -/
theorem onCore_lock_indistinguishable (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : LockedSystemState) (k : LockKey) (l₁ l₂ : RwLockState) :
    ObservableState.onCore ctx c L (setLockAt s k l₁).kernel
      = ObservableState.onCore ctx c L (setLockAt s k l₂).kernel := rfl

/-- SM8.D.1 (**the bracket**): `withLockSet` is a lock-only step whenever its
guarded action leaves the kernel state alone — the phases contribute only table
writes. -/
theorem withLockSet_lockWritesOnly {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState)
    (hAction : (action s.kernel).1 = s.kernel) :
    lockWritesOnly s (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1 :=
  hAction

-- ============================================================================
-- §2  SM8.D.2 — reader multiplicity is not directly observable
-- ============================================================================
--
-- The plan's D.2 row predates SM8.B.4.  With the `lock` field carried into the
-- projection, "how many cores hold this object for reading" would have been a
-- component of the observable state and the row would have been a genuine
-- proof obligation about a visible quantity.  With the lock state in the ghost
-- table, reader multiplicity is not a component of `ObservableState` at all,
-- and §1 settles it — but it is worth stating at the multiplicity itself
-- rather than leaving it as a corollary a reader has to assemble, because the
-- plan asked a specific question and the answer should be findable under the
-- name it was asked under.
--
-- What is *not* settled is the timing claim, and that is CC-5, restated below
-- and bounded in §3.

/-- SM8.D.2 (**the headline**): **reader multiplicity is not directly
observable.**  Two locked states that differ only in how many cores — and which
cores — hold a key for reading are identical to the observer `(c, L)` on every
core.

Stated over arbitrary reader lists rather than over a particular acquire, so it
covers every multiplicity the lock can reach, including the reachable
two-reader state SM2.C.6 constructs (see
`readerMultiplicity_not_observable_at_reachable_witness`). -/
theorem readerMultiplicity_not_observable (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : LockedSystemState) (k : LockKey)
    (readers₁ readers₂ : List CoreId) :
    ObservableState.onCore ctx c L
        (setLockAt s k { RwLockState.unheld with readers := readers₁ }).kernel
      = ObservableState.onCore ctx c L
        (setLockAt s k { RwLockState.unheld with readers := readers₂ }).kernel :=
  onCore_lock_indistinguishable ctx c L s k _ _

/-- SM8.D.2: the same statement against the **reachable** multi-reader state
SM2.C.6 exhibits, so the theorem is not about lock words the protocol can never
produce.

The existential carries `RwLockReachable` and not merely `wf`, which is the
difference between a non-vacuity witness and a well-formedness one: a `wf` state
need not be a state any execution produces, so a consumer holding only `wf` could
discharge this with a lock word the protocol never reaches — and the claim being
made here is precisely that the invisible multiplicity is one the protocol *does*
reach.  `rwLock_reader_multiplicity_reachable` supplies the derivation. -/
theorem readerMultiplicity_not_observable_at_reachable_witness (ctx : LabelingContext)
    (c : CoreId) (L : SecurityLabel) (s : LockedSystemState) (k : LockKey) :
    ∃ shared : RwLockState, SeLe4n.Kernel.Concurrency.RwLockReachable shared ∧
      shared.wf ∧ 2 ≤ shared.readers.length ∧
      ObservableState.onCore ctx c L (setLockAt s k shared).kernel
        = ObservableState.onCore ctx c L (setLockAt s k RwLockState.unheld).kernel := by
  obtain ⟨shared, hReach, hWf, hLen⟩ :=
    SeLe4n.Kernel.Concurrency.rwLock_reader_multiplicity_reachable
  exact ⟨shared, hReach, hWf, hLen, onCore_lock_indistinguishable ctx c L s k _ _⟩

/-- SM8.D.2 (the CC-5 restatement, which is the only open form): reader
multiplicity is invisible in the model, and the channel that remains is the
*timing* one the inventory already registers as CC-5 — `modelVisible := false`,
with §3's bound on what that timing can carry.

Stated as a conjunction so the inventory entry and this result cannot drift:
reclassifying CC-5 as model-visible without changing the projection breaks
this theorem. -/
theorem readerMultiplicity_is_timing_only (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : LockedSystemState) (k : LockKey) (l₁ l₂ : RwLockState) :
    acceptedCovertChannel_lockContention.modelVisible = false ∧
      acceptedCovertChannel_lockContention.perCoreInstance = true ∧
      ObservableState.onCore ctx c L (setLockAt s k l₁).kernel
        = ObservableState.onCore ctx c L (setLockAt s k l₂).kernel :=
  ⟨rfl, rfl, onCore_lock_indistinguishable ctx c L s k l₁ l₂⟩

-- ============================================================================
-- §3  SM8.D.3 — writer exclusion, and what a blocked acquirer really observes
-- ============================================================================
--
-- The plan's D.3 row reads "writer-exclusion observable to blocked readers".
-- At the model level that is **false**, and it is false in the safe direction:
-- the lock state lives in the ghost table (WS-LS LS3.1), so a blocked reader
-- observes *nothing* of the writer holding the key — not the holder's
-- identity, not the queue it is sitting in, not its own position in that
-- queue.  §3.1 states the refutation rather than reinstating the field.
--
-- What a blocked acquirer does observe is **delay**, and that is CC-5.  §3.2
-- makes it a quantity and bounds it; §3.3 turns the bound into an alphabet, a
-- pacing fact and a run capacity, in the same three-part shape SM8.B.9 gave
-- CC-1, so the two accepted timing channels are costed the same way rather
-- than one being quantified and the other described.
--
-- **Read the bound's premises.**  It holds under the SM2.C `FairTrace`
-- assumption — every acquired critical section is released within `maxDelay`
-- steps — which is a property of the *runtime*, assumed by SM2.C and not
-- established anywhere in the kernel.  `lockContention_unbounded_without_fairness`
-- below is the execution that shows the premise is load-bearing rather than
-- decorative: drop fairness and the queued core is never admitted at all.

/-- SM8.D.3 (**the refutation, part 1**): writer exclusion is not observable.
A state whose key is write-held by an arbitrary core is indistinguishable from
one whose key is free, to the observer `(c, L)` on every core. -/
theorem writerExclusion_not_observable (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : LockedSystemState) (k : LockKey) (holder : CoreId) :
    ObservableState.onCore ctx c L
        (setLockAt s k { RwLockState.unheld with writerHeld := some holder }).kernel
      = ObservableState.onCore ctx c L (setLockAt s k RwLockState.unheld).kernel :=
  onCore_lock_indistinguishable ctx c L s k _ _

/-- SM8.D.3 (**the refutation, part 2**): and a *blocked* acquirer observes
nothing either — not even its own presence in the queue.

This is the precise sense in which the plan's row is false as written: the
observer here is the very core that is blocked (`c` appears in `waiters`), and
its view is unchanged.  Whatever a blocked reader learns from writer exclusion,
it does not learn it from the kernel state. -/
theorem blockedAcquirer_observes_nothing (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : LockedSystemState) (k : LockKey) (holder : CoreId) (mode : AccessMode) :
    ObservableState.onCore ctx c L
        (setLockAt s k
          { RwLockState.unheld with writerHeld := some holder, waiters := [(c, mode)] }).kernel
      = ObservableState.onCore ctx c L (setLockAt s k RwLockState.unheld).kernel :=
  onCore_lock_indistinguishable ctx c L s k _ _

/-- SM8.D.3 (**what the blocked reader does learn, and when**): the reader at
the head of the queue becomes a holder at the very step the writer releases.

This is the operational content the plan's row was reaching for.  The reader
learns nothing from the state while it waits (the two theorems above), and the
instant the exclusion ends it is admitted — so the *only* thing writer exclusion
communicates to it is the moment of release, which is a time and not a value.
Stated at the object level, over the SM2.C `RwLockState` the kernel stores, and
with no fairness assumption: it is a single-step fact about
`promoteWaitersOnWriterRelease`. -/
theorem blockedReader_admitted_by_writer_release (c holder : CoreId) (l : RwLockState)
    (hHead : l.waiters.head? = some (c, AccessMode.read))
    (hHeld : l.writerHeld = some holder) :
    c ∈ (l.applyOp (.releaseWrite holder)).readers :=
  SeLe4n.Kernel.Concurrency.reader_at_head_admitted_by_writer_release l c holder hHead hHeld

-- ----------------------------------------------------------------------------
-- SM8.D.3 — the delay is the observation, and the delay is bounded
-- ----------------------------------------------------------------------------

/-- SM8.D.3: **the worst-case admission delay** of a contended acquire, in
execution steps.

`queueWaitDepth` counts what must drain before the acquirer is promoted —
queue position plus current holders — and SM2.C-defer D-3.9's
`queueWaitDepth_bounded` caps it at `numCores - 1` on any well-formed state,
for a queued reader exactly as for a queued writer.  Each unit of depth costs at
most `maxDelay + 1` steps by SM2.C-defer D-3.6, so this product is the whole
wait. -/
def lockContentionDelayBound (maxDelay : Nat) : Nat := (numCores - 1) * (maxDelay + 1)

/-- SM8.D.3: **the alphabet of one contention observation** — every reachable
delay, plus one code for "not admitted within the recorded execution".

`lockContentionDelayBound maxDelay + 2`, not `+ 1`: the delays run over
`0 … bound` inclusive (that is `bound + 1` values) and code `0` is reserved for
the un-admitted case, so that an observation which carries no delay is not
confused with one that carries a delay of zero. -/
def lockContentionAlphabet (maxDelay : Nat) : Nat := lockContentionDelayBound maxDelay + 2

/-- SM8.D.3: **the observation a contending core makes** — the delay between
enqueueing on a lock at step `enqueueStep` and being admitted to it, or `none`
when the recorded execution ends first.

Keyed to `admissionStepAfter`, the admission that **follows this enqueue**, not
to `admissionStep`, which is the core's first admission in the whole execution.
The distinction is not pedantic: a core that acquires, releases and re-acquires
has its first admission *before* the second enqueue, so the `admissionStep`
difference truncates to zero in `Nat` and reports no wait for an acquisition
that genuinely waited.  `lockContentionObservation_is_own_acquisition` is the
property that rules that out.

This is CC-5 as a value.  Nothing else about the lock reaches the core: §3.1 and
§3.2 above prove the state carries no information at all, so this delay is the
channel's *entire* content. -/
def lockContentionObservation (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId)
    (enqueueStep : Nat) : Option Nat :=
  (e.admissionStepAfter c enqueueStep).map (fun admitStep => admitStep - enqueueStep)

/-- SM8.D.3: the observation belongs to **this** acquisition — the admission it
measures from strictly follows the enqueue it is keyed to.

The load-bearing property of `admissionStepAfter` over `admissionStep`, and the
reason a repeat acquirer's second wait is reported rather than swallowed. -/
theorem lockContentionObservation_is_own_acquisition
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (kEnq delay : Nat)
    (h : lockContentionObservation e c kEnq = some delay) :
    ∃ admitStep, e.admissionStepAfter c kEnq = some admitStep ∧
      kEnq < admitStep ∧ delay = admitStep - kEnq ∧ e.holderAt admitStep c := by
  unfold lockContentionObservation at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨admitStep, hStep, hDelay⟩ := h
  obtain ⟨hGt, hHolder⟩ := e.admissionStepAfter_characterization c kEnq admitStep hStep
  exact ⟨admitStep, hStep, hGt, hDelay.symm, hHolder⟩

-- ----------------------------------------------------------------------------
-- SM8.D.3 — what unit the bound is in, and what it takes to read it as time
-- ----------------------------------------------------------------------------
--
-- `lockContentionObservation` subtracts two indices into `RwLockExecution.ops`,
-- so the figure it produces counts **operations on this lock** — equivalently,
-- the critical sections the waiter queues behind — and not elapsed time.  A
-- holder may occupy its critical section for an arbitrarily long real interval
-- without any operation on the lock being recorded, so a step-delay of one can
-- correspond to an unbounded wall-clock wait.  Every result downstream
-- (`lockContention_delay_bounded`, the alphabet, the trace capacity) inherits
-- that unit.
--
-- Reading CC-5 as a *timing* channel therefore needs one more assumption the
-- SM2.C model does not carry: a ceiling on how long a single critical section
-- can run.  Rather than leave that implicit in prose — which is what made the
-- earlier "wall-clock delay" wording overclaim — it is a parameter here, and the
-- bridge theorem below is stated with it as an explicit hypothesis.
--
-- The stronger result landed at **WS-LC LC5**: `RwLockExecution` carries a
-- per-step cost (`stepCost`, with no default, so every construction site
-- declares its cost model), and `lockContention_elapsed_bounded` below is this
-- bound read through the execution's own costs rather than through a cost
-- function a caller happened to supply.  Both forms are kept, and the pair is
-- the point: the generic one is the general statement about *any* cost model,
-- the execution-level one is the statement about *this* execution's, and a
-- caller that has an execution should not have to re-supply what the execution
-- already carries.
--
-- What is still an assumption rather than a theorem is the ceiling itself.
-- `BoundedCriticalSection` is a Prop about the field, not a structure
-- invariant: an execution whose critical sections are unbounded is a perfectly
-- good execution and every step bound still holds of it.  What fails without
-- the ceiling is only the *reading* of that bound as wall-clock — which is the
-- distinction this comment block existed to record, and the one the
-- denomination makes checkable instead of merely stated.

/-- SM8.D.3: the observation as a single natural number, with `0` reserved for
"no admission in this execution". -/
def lockContentionCode (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId)
    (enqueueStep : Nat) : Nat :=
  match lockContentionObservation e c enqueueStep with
  | some delay => delay + 1
  | none => 0

/-- SM8.D.3: the encoding **loses nothing** — two acquisitions the contending
core can tell apart get different codes.  This is what makes §3.3's count a
capacity bound on the channel rather than a count of an arbitrary encoding. -/
theorem lockContentionCode_injective (e₁ e₂ : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (c : CoreId) (k₁ k₂ : Nat)
    (h : lockContentionCode e₁ c k₁ = lockContentionCode e₂ c k₂) :
    lockContentionObservation e₁ c k₁ = lockContentionObservation e₂ c k₂ := by
  unfold lockContentionCode at h
  cases h₁ : lockContentionObservation e₁ c k₁ <;>
    cases h₂ : lockContentionObservation e₂ c k₂ <;>
    rw [h₁, h₂] at h <;> simp_all

/-- SM8.D.3 (**the CC-5 delay bound**): a contending writer's observation is
bounded.

Under the SM2.C `FairTrace` assumption — every acquired critical section is
released within `maxDelay` steps — a writer that enqueues at step `kEnq` is
admitted, and the delay it measures is at most
`(numCores - 1) × (maxDelay + 1)`.

Both factors are the SM2.C results, composed rather than restated: the wait
depth is capped by `writerWaitDepth_bounded` (SM2.C-defer D-2.3, the *tight*
`numCores - 1` bound, not the naive `2·numCores - 1`), and each unit of depth
costs at most `maxDelay + 1` steps by `rwLock_writer_admissionStepAfter_bounded`
(SM2.C-defer D-3.8, itself derived from the D-3.6 liveness theorem rather than
from its `admissionStep` corollary — see `lockContentionObservation`).

The `hWithin` premise says the recorded execution is long enough to contain the
admission; it is the bound's own worst case, so it is exactly the hypothesis
"this execution did not end mid-wait" and not a smuggled assumption about how
long the wait was.

**Any contending mode.**  The bound holds for a queued reader on the same terms
as a queued writer: SM2.C-defer D-3.10 generalises the liveness chain — keystone
included — to an arbitrary access mode, and `queueWaitDepth_bounded` caps the
depth without ever mentioning the waiter's mode.  `blockedReaderContention_delay_bounded`
and `writerContention_delay_bounded` are the two instances.

**The waiter does not withdraw** (`hNoCancel`).  `RwLockOp.cancel` lets a queued
core take its request back, and a core that withdraws is never admitted — so the
conclusion "there *is* an observation, and it is bounded" is false of a window
containing `c`'s own cancellation, at any fairness budget.  The hypothesis is the
one `rwLock_queued_admissionStepAfter_bounded` carries, stated here over the
*outer* window `[kEnq, kEnq + lockContentionDelayBound maxDelay + 1)` so a caller
supplies it once against the figure the bound is denominated in, rather than
against an inner window computed from `queueWaitDepth`; `noCancelIn.mono`
narrows it.

This is a premise about the *observation*, not a weakening of the channel bound:
a withdrawn acquisition produces no contention observation to bound, and
`lockContentionRun` carries the same condition per step so an accepted run
supplies it for free. -/
theorem lockContention_delay_bounded (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (maxDelay : Nat) (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (m : AccessMode) (kEnq : Nat)
    (hQueued : (c, m) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length)
    (hNoCancel : e.noCancelIn c kEnq (kEnq + lockContentionDelayBound maxDelay + 1)) :
    ∃ delay, lockContentionObservation e c kEnq = some delay ∧
      delay ≤ lockContentionDelayBound maxDelay := by
  have hDepth : SeLe4n.Kernel.Concurrency.queueWaitDepth (e.stateAt kEnq) c m ≤ numCores - 1 :=
    SeLe4n.Kernel.Concurrency.queueWaitDepth_bounded (e.stateAt kEnq) (e.stateAt_wf kEnq) c m
      hQueued
  have hMul : SeLe4n.Kernel.Concurrency.queueWaitDepth (e.stateAt kEnq) c m * (maxDelay + 1)
      ≤ lockContentionDelayBound maxDelay :=
    Nat.mul_le_mul hDepth (Nat.le_refl _)
  have hInner : kEnq + SeLe4n.Kernel.Concurrency.queueWaitDepth (e.stateAt kEnq) c m *
      (maxDelay + 1) < e.ops.length :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hMul kEnq) hWithin
  obtain ⟨admitStep, hStep, _, hLe⟩ :=
    SeLe4n.Kernel.Concurrency.rwLock_queued_admissionStepAfter_bounded e maxDelay hFair hInit c m
      kEnq hQueued hInner (hNoCancel.mono (Nat.le_refl _) (by omega))
  have hBound : admitStep ≤ kEnq + lockContentionDelayBound maxDelay :=
    Nat.le_trans hLe (Nat.add_le_add_left hMul kEnq)
  refine ⟨admitStep - kEnq, ?_, by omega⟩
  unfold lockContentionObservation
  rw [hStep]
  rfl


/-- SM8.D.3 (**CC-5 as a wall-clock bound — and what that costs in assumptions**).

`lockContention_delay_bounded` bounds the wait in *lock operations*.  This is the
timing statement, and it needs a ceiling `tCs` on how long any single interval
between operations runs — which the SM2.C execution model does not supply, so it
is a hypothesis rather than something derived.

The composition is deliberately kept as its own theorem rather than folded into
the bound above: the step bound is unconditional given fairness, while the time
bound is not, and merging them would hide which assumption carries which half. -/
theorem lockContention_wallClock_bounded (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (maxDelay : Nat) (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (m : AccessMode) (kEnq : Nat)
    (hQueued : (c, m) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length)
    (hNoCancel : e.noCancelIn c kEnq (kEnq + lockContentionDelayBound maxDelay + 1))
    (cost : Nat → Nat) (tCs : Nat) (hCost : ∀ k, cost k ≤ tCs) :
    ∃ delay admitStep, lockContentionObservation e c kEnq = some delay ∧
      e.admissionStepAfter c kEnq = some admitStep ∧
      delay ≤ lockContentionDelayBound maxDelay ∧
      SeLe4n.Kernel.Concurrency.elapsedBetween cost kEnq admitStep ≤ lockContentionDelayBound maxDelay * tCs := by
  obtain ⟨delay, hObs, hLe⟩ :=
    lockContention_delay_bounded e maxDelay hFair hInit c m kEnq hQueued hWithin hNoCancel
  obtain ⟨admitStep, hStep, _, hDelay, _⟩ :=
    lockContentionObservation_is_own_acquisition e c kEnq delay hObs
  refine ⟨delay, admitStep, hObs, hStep, hLe, ?_⟩
  calc SeLe4n.Kernel.Concurrency.elapsedBetween cost kEnq admitStep
      ≤ (admitStep - kEnq) * tCs := SeLe4n.Kernel.Concurrency.elapsedBetween_le cost tCs hCost kEnq admitStep
    _ ≤ lockContentionDelayBound maxDelay * tCs := by
        exact Nat.mul_le_mul_right tCs (hDelay ▸ hLe)

/-- **WS-LC LC5.6** (**the same bound, in the execution's own cycles**).

`lockContention_wallClock_bounded` above takes a cost function as an argument,
because when it was written `RwLockExecution` had none.  It does now, so this
is the form a caller who *has* an execution should reach for: the cost model is
the execution's, not one the caller re-supplies and might supply differently
from the one the rest of its reasoning assumes.

The generic form is kept deliberately.  It is the general statement — a bound
under *any* cost model, including one attributed to an execution externally —
and it is what a caller reasoning about a family of cost models needs.  This
one is the instance at the execution's own. -/
theorem lockContention_elapsed_bounded (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (maxDelay : Nat) (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (m : AccessMode) (kEnq : Nat)
    (hQueued : (c, m) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length)
    (hNoCancel : e.noCancelIn c kEnq (kEnq + lockContentionDelayBound maxDelay + 1))
    (tCs : Nat) (hCost : e.BoundedCriticalSection tCs) :
    ∃ delay admitStep, lockContentionObservation e c kEnq = some delay ∧
      e.admissionStepAfter c kEnq = some admitStep ∧
      delay ≤ lockContentionDelayBound maxDelay ∧
      e.elapsed kEnq admitStep ≤ lockContentionDelayBound maxDelay * tCs :=
  lockContention_wallClock_bounded e maxDelay hFair hInit c m kEnq hQueued hWithin
    hNoCancel e.stepCost tCs hCost

/-- **WS-LC LC5.6**: and at unit cost it is the step bound.

The instantiation check for the CC-5 chain, matching the one the lock model
carries for the admission bound: a denomination that had quietly weakened the
claim would look exactly like one that had not, so the collapse back to steps
is stated rather than assumed. -/
theorem lockContention_elapsed_at_unit_cost
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (maxDelay : Nat) (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (m : AccessMode) (kEnq : Nat)
    (hQueued : (c, m) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length)
    (hNoCancel : e.noCancelIn c kEnq (kEnq + lockContentionDelayBound maxDelay + 1))
    (hUnit : e.stepCost = fun _ => 1) :
    ∃ delay admitStep, lockContentionObservation e c kEnq = some delay ∧
      e.admissionStepAfter c kEnq = some admitStep ∧
      admitStep - kEnq ≤ lockContentionDelayBound maxDelay := by
  obtain ⟨delay, admitStep, hObs, hStep, hLe, hElapsed⟩ :=
    lockContention_elapsed_bounded e maxDelay hFair hInit c m kEnq hQueued hWithin
      hNoCancel 1 (fun k => by rw [hUnit]; exact Nat.le_refl 1)
  refine ⟨delay, admitStep, hObs, hStep, ?_⟩
  rw [e.elapsed_unit_cost hUnit] at hElapsed
  omega

/-- SM8.D.3: the writer instance of the delay bound. -/
theorem writerContention_delay_bounded (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (maxDelay : Nat) (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (kEnq : Nat)
    (hQueued : (c, AccessMode.write) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length)
    (hNoCancel : e.noCancelIn c kEnq (kEnq + lockContentionDelayBound maxDelay + 1)) :
    ∃ delay, lockContentionObservation e c kEnq = some delay ∧
      delay ≤ lockContentionDelayBound maxDelay :=
  lockContention_delay_bounded e maxDelay hFair hInit c AccessMode.write kEnq hQueued hWithin
    hNoCancel

/-- SM8.D.3 (**the blocked reader's temporal bound**): a *reader* waiting behind
a writer measures a delay bounded by the same figure.

This is the half of the plan's §SM8.D.3 claim that the SM2.C surface could not
supply until D-3.10 generalised the liveness chain: the reader had a queue-position
cap (`readerContentionDepth_bounded`) and a head-of-queue admission fact
(`blockedReader_admitted_by_writer_release`), but no bound in *time*.  With this,
CC-5's alphabet figure covers every contending core rather than the writers
only, which is what an accepted-channel bandwidth claim has to do. -/
theorem blockedReaderContention_delay_bounded (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (maxDelay : Nat) (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (kEnq : Nat)
    (hQueued : (c, AccessMode.read) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length)
    (hNoCancel : e.noCancelIn c kEnq (kEnq + lockContentionDelayBound maxDelay + 1)) :
    ∃ delay, lockContentionObservation e c kEnq = some delay ∧
      delay ≤ lockContentionDelayBound maxDelay :=
  lockContention_delay_bounded e maxDelay hFair hInit c AccessMode.read kEnq hQueued hWithin
    hNoCancel

/-- SM8.D.3 (**the reader's structural bound**): at most `numCores - 1` cores
can be ahead of a blocked reader.

The mode-generic depth cap (SM2.C-defer D-3.9): the pigeonhole argument counts
distinct cores and never mentions the waiter's own access mode.  It bounds *how
much* has to drain before the reader is admitted; the per-unit cost that turns it
into a temporal figure is D-3.10's mode-generic liveness chain, so
`blockedReaderContention_delay_bounded` composes the two exactly as the writer
instance does. -/
theorem readerContentionDepth_bounded (l : RwLockState) (hWf : l.wf) (c : CoreId)
    (hQueued : (c, AccessMode.read) ∈ l.waiters) :
    SeLe4n.Kernel.Concurrency.readerWaitDepth l c ≤ numCores - 1 :=
  SeLe4n.Kernel.Concurrency.readerWaitDepth_bounded l hWf c hQueued

/-- SM8.D.3 (**the CC-5 alphabet bound**): one contention observation therefore
carries at most `log₂(lockContentionAlphabet maxDelay)` bits.

This is CC-5's counterpart of `schedulingChannel_alphabet_bounded`, and it is
what the plan's §4.2 "documented and accepted" position rests on: the channel is
not closed, but it is not unbounded either. -/
theorem lockContentionChannel_alphabet_bounded (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (maxDelay : Nat) (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (m : AccessMode) (kEnq : Nat)
    (hQueued : (c, m) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length)
    (hNoCancel : e.noCancelIn c kEnq (kEnq + lockContentionDelayBound maxDelay + 1)) :
    lockContentionCode e c kEnq < lockContentionAlphabet maxDelay := by
  obtain ⟨delay, hObs, hLe⟩ :=
    lockContention_delay_bounded e maxDelay hFair hInit c m kEnq hQueued hWithin hNoCancel
  unfold lockContentionCode lockContentionAlphabet
  rw [hObs]
  show delay + 1 < lockContentionDelayBound maxDelay + 2
  omega

/-- SM8.D.3: the reserved code, so the `+ 2` in the alphabet is used rather than
slack.  An acquisition the recorded execution never admits reads as `0`, which
`lockContentionCode_injective` keeps distinct from a zero-step delay. -/
theorem lockContentionCode_eq_zero_iff (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (c : CoreId) (kEnq : Nat) :
    lockContentionCode e c kEnq = 0 ↔ e.admissionStepAfter c kEnq = none := by
  unfold lockContentionCode lockContentionObservation
  cases e.admissionStepAfter c kEnq <;> simp

/-- SM8.D.3: the *allocated* alphabet never collapses to one code, whatever the
fairness parameter.

**What this does not establish.**  It is an arithmetic fact about the code
space's size, and a code being allocated is not a code being reachable — under
the premises an accepted run carries, `0` (never admitted) is excluded by the
delay bound and `1` (zero delay) by `acceptedContentionCode_ge_two`, so the two
codes counted here are exactly the two such a run cannot produce.  The claim that
CC-5 is *open* — that it distinguishes at least two behaviours, and so carries at
least one bit — is `lockContentionChannel_two_codes_reachable`, which exhibits
two fair, in-premise executions with different codes.  This theorem remains
useful as the alphabet's floor; it is simply not the non-closure witness. -/
theorem lockContentionAlphabet_at_least_two (maxDelay : Nat) :
    2 ≤ lockContentionAlphabet maxDelay := by
  unfold lockContentionAlphabet; omega

/-- SM8.D.3: the **core-count** factor of the bound at the shipped hardware —
four RPi5 cores, so at most three can be ahead of a contending one.

This half of the figure is grounded: `numCores` is the platform's real core
count.  The other half is not — see `lockContentionAlphabet_at_release_budget`. -/
theorem lockContentionDelayBound_rpi5_coreFactor (maxDelay : Nat) :
    lockContentionDelayBound maxDelay = 3 * (maxDelay + 1) := by
  unfold lockContentionDelayBound; rfl

/-- SM8.D.3: the alphabet at SM2.C-defer D-3.7's release-delay symbol.

**`MAX_RELEASE_DELAY` is a placeholder, not a measured deployment figure.**  Its
own docstring reads "a placeholder value of `1024` (steps); SM3 will tune this
against actual kernel critical-section budgets", so `3077` is the alphabet *that
symbol currently yields*, not a property of the shipped kernel.  The
`numCores - 1 = 3` factor is real (see above); the `maxDelay + 1 = 1025` factor
moves when SM3 tunes the budget, and `lockContentionAlphabet` is parametric in
it precisely so that the bound does not have to be restated when it does. -/
theorem lockContentionAlphabet_at_release_budget :
    lockContentionAlphabet SeLe4n.Kernel.Concurrency.MAX_RELEASE_DELAY = 3077 := by
  decide

-- ----------------------------------------------------------------------------
-- SM8.D.3 — the fairness premise is load-bearing
-- ----------------------------------------------------------------------------

/-- SM8.D.3: an execution in which core 0 takes the write lock and never
releases it, and core 1 queues behind it forever. -/
def starvingExecution : SeLe4n.Kernel.Concurrency.RwLockExecution :=
  { initial := RwLockState.unheld
    ops := [.tryAcquireWrite bootCoreId, .tryAcquireWrite ⟨1, by decide⟩]
    initial_reachable := .base
    -- WS-LC LC5.1: unit cost.  These witnesses exist to exhibit a *step*
    -- count, and at unit cost the cycle figure is that step count
    -- (`RwLockExecution.elapsed_unit_cost`) — so the observation they
    -- carry means the same thing in either denomination, which is exactly
    -- what a witness for a step bound should say.
    stepCost := fun _ => 1 }

/-- SM8.D.3: core 1 really is queued in it. -/
theorem starvingExecution_queued :
    (⟨1, by decide⟩, AccessMode.write) ∈ (starvingExecution.stateAt 2).waiters := by decide

/-- SM8.D.3 (**the premise is load-bearing**): without fairness there is no
bound at all — the queued core is never admitted, and its observation is the
reserved "no admission" code rather than any delay.

`lockContention_delay_bounded` is therefore a statement about runtimes that
satisfy the SM2.C release-delay assumption, and nothing in the kernel
establishes that assumption.  Recording it as a theorem rather than a caveat is
the point: a reader who takes the bound as unconditional is taking it wrongly,
and this execution is the counterexample. -/
theorem lockContention_unbounded_without_fairness :
    starvingExecution.admissionStepAfter ⟨1, by decide⟩ 2 = none ∧
      lockContentionObservation starvingExecution ⟨1, by decide⟩ 2 = none ∧
      lockContentionCode starvingExecution ⟨1, by decide⟩ 2 = 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · unfold lockContentionObservation
    rw [show starvingExecution.admissionStepAfter ⟨1, by decide⟩ 2 = none from by decide]
    rfl
  · rw [lockContentionCode_eq_zero_iff]
    decide

/-- SM8.D.3: and the execution is genuinely unfair — the holder never releases,
so no release-delay budget makes it a `FairTrace`.  Stated at the SM2.C-defer
D-3.7 symbol; the same argument holds at every budget, since core 0 holds the
write lock at *every* step from 1 onward. -/
theorem starvingExecution_writer_never_releases (k : Nat) (hk : 1 ≤ k) :
    (starvingExecution.stateAt k).writerHeld = some bootCoreId := by
  match k, hk with
  | 1, _ => decide
  | 2, _ => decide
  | (n + 3), _ =>
    rw [starvingExecution.stateAt_of_ge_length (by simp [starvingExecution])]
    decide

-- ----------------------------------------------------------------------------
-- SM8.D.3 — two observations that are actually reachable
-- ----------------------------------------------------------------------------
--
-- `lockContentionAlphabet_at_least_two` counts *allocated* codes, and counting
-- allocated codes cannot show a channel is open: under the premises an accepted
-- run carries, code `0` (never admitted) is excluded by the delay bound itself,
-- and code `1` (zero delay) is excluded because `admissionStepAfter` is strictly
-- later than the enqueue.  So the two codes it counts are precisely the two that
-- a fair, in-premise acquisition cannot produce.
--
-- The non-closure claim therefore needs *executions*, not arithmetic: two fair
-- traces, each satisfying the bound's own premises, on which a contending core
-- reads different codes.  These two supply them — `waiterCore` behind a holder
-- (delay 1), and the *same* `waiterCore` behind a holder **and** a core queued
-- ahead of it (delay 2).
--
-- **The observing core is held fixed on purpose.**  A per-core channel carries a
-- bit when *one* observer can be in two distinguishable situations; two codes
-- read by two different cores would only show that the code depends on which
-- core you are, which is not a channel anyone can receive on.  An earlier cut
-- compared `waiterCore` in the first trace against a second waiter in the
-- second, and so proved the weaker thing.  `aheadCore` is therefore the core
-- placed *ahead* of the waiter in the second trace, never the one observed.

/-- The contending core the non-closure witness OBSERVES, in both traces.
Not private: the claim rests on both readings being this core's, and the suite
checks that rather than taking it on trust. -/
def waiterCore : CoreId := ⟨1, by decide⟩

/-- The core queued **ahead** of `waiterCore` in the two-waiter trace — never the
one observed. -/
def aheadCore : CoreId := ⟨2, by decide⟩

private def padCore : CoreId := ⟨3, by decide⟩

/-- SM8.D.3: core 1 asks for the write lock while core 0 holds it, and is
admitted by core 0's release — a delay of one step.  The trailing no-ops
(`releaseRead` on a core that never read-held) make the trace long enough for the
bound's own `hWithin` premise. -/
def singleWaiterExecution : SeLe4n.Kernel.Concurrency.RwLockExecution :=
  { initial := RwLockState.unheld
    ops := [ .tryAcquireWrite bootCoreId, .tryAcquireWrite waiterCore
           , .releaseWrite bootCoreId, .releaseWrite waiterCore
           , .releaseRead padCore, .releaseRead padCore, .releaseRead padCore
           , .releaseRead padCore, .releaseRead padCore, .releaseRead padCore
           , .releaseRead padCore, .releaseRead padCore ]
    initial_reachable := .base
    -- WS-LC LC5.1: unit cost.  These witnesses exist to exhibit a *step*
    -- count, and at unit cost the cycle figure is that step count
    -- (`RwLockExecution.elapsed_unit_cost`) — so the observation they
    -- carry means the same thing in either denomination, which is exactly
    -- what a witness for a step bound should say.
    stepCost := fun _ => 1 }

/-- SM8.D.3: and the same waiter with `aheadCore` queued **ahead** of it, so its
admission waits for two releases — a delay of two steps.

The enqueue order is what carries the finding: `aheadCore` goes in first, so the
core observed in both traces is `waiterCore` in both.  Reading a second waiter's
code here instead would compare two observers and show only that the code depends
on which core you are. -/
def twoWaiterExecution : SeLe4n.Kernel.Concurrency.RwLockExecution :=
  { initial := RwLockState.unheld
    ops := [ .tryAcquireWrite bootCoreId, .tryAcquireWrite aheadCore
           , .tryAcquireWrite waiterCore
           , .releaseWrite bootCoreId, .releaseWrite aheadCore
           , .releaseWrite waiterCore
           , .releaseRead padCore, .releaseRead padCore, .releaseRead padCore
           , .releaseRead padCore, .releaseRead padCore, .releaseRead padCore
           , .releaseRead padCore ]
    initial_reachable := .base
    -- WS-LC LC5.1: unit cost.  These witnesses exist to exhibit a *step*
    -- count, and at unit cost the cycle figure is that step count
    -- (`RwLockExecution.elapsed_unit_cost`) — so the observation they
    -- carry means the same thing in either denomination, which is exactly
    -- what a witness for a step bound should say.
    stepCost := fun _ => 1 }

/-- SM8.D.3: both traces are fair at the same budget, so the two observations are
comparable and neither is obtained by relaxing the premises. -/
theorem contentionWitnesses_fair :
    SeLe4n.Kernel.Concurrency.FairTrace singleWaiterExecution 2 ∧
    SeLe4n.Kernel.Concurrency.FairTrace twoWaiterExecution 2 :=
  ⟨(SeLe4n.Kernel.Concurrency.fairTrace_iff_bounded singleWaiterExecution 2).mpr (by decide),
   (SeLe4n.Kernel.Concurrency.fairTrace_iff_bounded twoWaiterExecution 2).mpr (by decide)⟩

/-- SM8.D.3: each witness's listed step is a genuine enqueue **edge** at the
mode claimed, and each trace is long enough for the bound — the two premises an
accepted run imposes. -/
theorem contentionWitnesses_in_premises :
    ((waiterCore, AccessMode.write) ∈ (singleWaiterExecution.stateAt 2).waiters ∧
      (waiterCore, AccessMode.write) ∉ (singleWaiterExecution.stateAt 1).waiters ∧
      2 + lockContentionDelayBound 2 < singleWaiterExecution.ops.length) ∧
    ((waiterCore, AccessMode.write) ∈ (twoWaiterExecution.stateAt 3).waiters ∧
      (waiterCore, AccessMode.write) ∉ (twoWaiterExecution.stateAt 2).waiters ∧
      3 + lockContentionDelayBound 2 < twoWaiterExecution.ops.length) := by decide

/-- SM8.D.3 (**the non-closure witness**): a contending core reads **different**
codes on two fair, in-premise acquisitions — so CC-5 distinguishes at least two
behaviours and carries at least one bit.

This is what `lockContentionAlphabet_at_least_two` was doing duty for and could
not establish: an arithmetic lower bound on the *allocated* alphabet says nothing
about which codes an execution can actually produce, and the two it counts are
exactly the two an accepted run never produces. -/
theorem lockContentionChannel_two_codes_reachable :
    lockContentionCode singleWaiterExecution waiterCore 2 = 2 ∧
    lockContentionCode twoWaiterExecution waiterCore 3 = 3 ∧
    lockContentionCode singleWaiterExecution waiterCore 2
      ≠ lockContentionCode twoWaiterExecution waiterCore 3 := by decide

/-- SM8.D.3: and the delays behind those codes, so the figures are readable
rather than only distinct. -/
theorem contentionWitnesses_delays :
    lockContentionObservation singleWaiterExecution waiterCore 2 = some 1 ∧
    lockContentionObservation twoWaiterExecution waiterCore 3 = some 2 := by decide

/-- SM8.D.3 (**why codes 0 and 1 are not the witnesses**): an accepted
acquisition is admitted strictly after its enqueue, so its delay is at least one
and its code at least two.  The reserved `0` and the "zero delay" `1` are
allocated but unreachable under the bound's premises — which is the whole reason
the reachability witness above is stated over executions. -/
theorem acceptedContentionCode_ge_two (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (c : CoreId) (kEnq a : Nat) (h : e.admissionStepAfter c kEnq = some a) :
    2 ≤ lockContentionCode e c kEnq := by
  have hGt : kEnq < a := (e.admissionStepAfter_characterization c kEnq a h).1
  unfold lockContentionCode lockContentionObservation
  rw [h]
  simp only [Option.map_some]
  omega

-- ----------------------------------------------------------------------------
-- SM8.D.3 — from one observation to a run, with a pacing bound
-- ----------------------------------------------------------------------------

/-- SM8.D.3: the premises a whole run of contended acquisitions must satisfy for
the capacity bound to apply, bundled so the trace theorem states them once.

A run is a list of **enqueue steps within one execution** — the same shared time
base CC-1's `schedulingCapacityRun` has over a list of states.  An earlier cut
modelled it as a list of unrelated executions, which made "n observations"
correspond to no shared window at all and left the count uncomparable with
CC-1's.

The access mode is existential **per step**: one core's successive contended
acquisitions need not all be writes, and after SM2.C-defer D-3.10 the delay bound
does not care which they are.

Each listed step must be a genuine **enqueue edge** — queued at `k`, *not*
queued at `k - 1`, at the same access mode — and the steps must be `Nodup`.  Both
conjuncts are load-bearing, and for different reasons.

`Nodup` alone is not enough, which is the subtler half.  Mere queue *membership*
holds at every step a core remains queued, so a single physical acquisition that
waits from step 2 to step 5 would admit the run `[2, 3, 4]`: three distinct steps,
three different delays, three different codes — from one acquisition.  The run
length would then not be the number of acquisitions and the capacity figure would
count the same behaviour repeatedly.  Keying on the transition edge makes each
listed step an acquisition the core actually *started*, which is what
`lockContentionObservation` measures from.

The mode is existential **per step**: one core's successive contended
acquisitions need not all be writes, and after SM2.C-defer D-3.10 the delay bound
does not care which they are.  It is bound inside the edge condition rather than
outside it so the "not queued before" half is about the *same* mode — a core
switching modes between acquisitions is still two edges, not one.

Each listed step also carries the delay bound's own two premises, so a run
supplies them and a consumer need not re-impose them: the recording is long
enough to contain the admission, and the core does not **withdraw** inside the
window (`RwLockOp.cancel` — a withdrawn acquisition never becomes an admission,
so it yields no observation to code).  A run is therefore exactly the set of
acquisitions the channel can actually be read off. -/
def lockContentionRun (maxDelay : Nat) (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (c : CoreId) (enqueueSteps : List Nat) : Prop :=
  SeLe4n.Kernel.Concurrency.FairTrace e maxDelay ∧
  e.initial = RwLockState.unheld ∧
  enqueueSteps.Nodup ∧
  ∀ k ∈ enqueueSteps,
    (1 ≤ k ∧ ∃ m : AccessMode,
      (c, m) ∈ (e.stateAt k).waiters ∧ (c, m) ∉ (e.stateAt (k - 1)).waiters) ∧
    k + lockContentionDelayBound maxDelay < e.ops.length ∧
    e.noCancelIn c k (k + lockContentionDelayBound maxDelay + 1)

/-- SM8.D.3: the sequence of codes a contending core reads off a run. -/
def lockContentionTrace (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId)
    (enqueueSteps : List Nat) : List Nat :=
  enqueueSteps.map (lockContentionCode e c)

/-- SM8.D.3 (**the CC-5 pacing bound, in lock operations**): a core cannot make
more observations than the execution has steps.

**This is a bound per lock operation**, and on its own it is close to a
tautology: distinct acquisitions have distinct enqueue steps, and an execution
of `n` operations has `n + 1` steps.  It does *not* by itself make CC-5's
capacity comparable with CC-1's, whose pacing
(`schedulingObservation_changes_on_domain_tick`) is per **timer tick** — real
time — because many lock operations may fall between two ticks.

The per-unit-time form exists (WS-LC LC5.7):
`lockContentionChannel_rate_per_elapsed_time` bounds observations against
elapsed time, and `lockContentionChannel_rate_per_execution_time` states it at
the execution's own cost model.  Like the delay bound it needs one: a *floor*
on how long an inter-operation interval takes.  The two are duals —
`SeLe4n.Kernel.Concurrency.elapsedBetween_le` needs a ceiling to bound one
wait, this needs a floor to bound how many waits fit in a window.

CC-1's capacity figure needs two factors — how much one observation carries and
how often one can be made — and `schedulingObservation_changes_on_domain_tick`
supplies the second for the scheduling channel.  This is CC-5's: each contended
acquisition is identified by its own enqueue step, distinct acquisitions have
distinct enqueue steps, and an execution of `n` operations has `n + 1` steps.

So the run capacity below is a bound *per execution*, not merely per
observation — but "per execution" is a count of lock operations, and turning it
into a rate needs the theorem below. -/
theorem lockContentionChannel_observation_rate_bounded
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (enqueueSteps : List Nat)
    (hNodup : enqueueSteps.Nodup) (hRange : ∀ k ∈ enqueueSteps, k ≤ e.ops.length) :
    (lockContentionTrace e c enqueueSteps).length ≤ e.ops.length + 1 := by
  simp only [lockContentionTrace, List.length_map]
  exact e.distinct_steps_length_le enqueueSteps hNodup hRange

/-- SM8.D.3 (**the rate CC-1 comparability actually needs**): observations per
unit of *elapsed time*, not per lock operation.

`lockContentionChannel_observation_rate_bounded` says a core cannot observe more
often than the lock is operated on, which is a bound in the wrong currency for a
bandwidth figure — many lock operations may fall between two timer ticks, so it
does not limit how much a channel carries per second.

This does: given a floor `tMin` on how long any inter-operation interval takes,
`n` observations require at least `n * tMin` of elapsed time **within the
execution's own window** — states `0 … ops.length`, which is `ops.length`
intervals, not one more.  Read as a rate, at most one observation per `tMin`.

The floor is a hypothesis, exactly as the ceiling is in
`lockContention_wallClock_bounded`, and for the same reason — but the reason is
no longer that the model has no notion of duration.  It has one since WS-LC
LC5.1 (`RwLockExecution.stepCost`); what it does not have, and cannot, is a
*derivation* of what a deployment's critical sections cost.  Both halves of
CC-5's bandwidth figure — how much one observation carries, and how often one
can be made — are therefore conditional on a declared cost model, and the
alphabet result is the only unconditional half.
`lockContentionChannel_rate_per_execution_time` is this statement at the
execution's own model. -/
theorem lockContentionChannel_rate_per_elapsed_time
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (cost : Nat → Nat) (tMin : Nat)
    (hCost : ∀ k, tMin ≤ cost k) (steps : List Nat)
    (hNodup : steps.Nodup) (hRange : ∀ k ∈ steps, k ≤ e.ops.length)
    (hPos : ∀ k ∈ steps, 1 ≤ k) :
    steps.length * tMin ≤ SeLe4n.Kernel.Concurrency.elapsedBetween cost 0 e.ops.length := by
  -- An execution of `n` operations spans states `0 … n`, so it has exactly `n`
  -- intervals — measuring through `n + 1` would sum a `cost n` that no step of
  -- the execution occupies, and let an observation be paid for with time after
  -- the recorded execution ended.
  --
  -- The enqueue-edge premise `1 ≤ k` is what makes the counting come out at `n`
  -- rather than `n + 1`: no observation is keyed to step `0`, so prepending it
  -- gives a `Nodup` list in `[0, n]` one longer than `steps`.
  have hZero : 0 ∉ steps := fun h => absurd (hPos 0 h) (by omega)
  have hCons : (0 :: steps).Nodup := List.nodup_cons.mpr ⟨hZero, hNodup⟩
  have hConsRange : ∀ k ∈ (0 :: steps), k ≤ e.ops.length := by
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk'
    · exact Nat.zero_le _
    · exact hRange k hk'
  have hLen : steps.length ≤ e.ops.length := by
    have := e.distinct_steps_length_le (0 :: steps) hCons hConsRange
    simp only [List.length_cons] at this
    omega
  calc steps.length * tMin ≤ e.ops.length * tMin := Nat.mul_le_mul_right tMin hLen
    _ ≤ SeLe4n.Kernel.Concurrency.elapsedBetween cost 0 e.ops.length := by
        simpa using SeLe4n.Kernel.Concurrency.elapsedBetween_ge cost tMin hCost 0 e.ops.length

/-- **WS-LC LC5.7** (**the rate, at the execution's own cost model**).

`lockContentionChannel_rate_per_elapsed_time` takes a cost function as an
argument, because when it was written an execution carried none.  This is that
statement read through the execution's own — the pacing dual of
`lockContention_elapsed_bounded`, and the reason no docstring in this section
still says the figure is available only per lock operation. -/
theorem lockContentionChannel_rate_per_execution_time
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (tMin : Nat)
    (hCost : e.CostedCriticalSection tMin) (steps : List Nat)
    (hNodup : steps.Nodup) (hRange : ∀ k ∈ steps, k ≤ e.ops.length)
    (hPos : ∀ k ∈ steps, 1 ≤ k) :
    steps.length * tMin ≤ e.elapsed 0 e.ops.length :=
  lockContentionChannel_rate_per_elapsed_time e e.stepCost tMin hCost steps hNodup
    hRange hPos

/-- SM8.D.3 (**the CC-5 capacity bound**): over a run of `n` contended
acquisitions the core's whole trace is one element of
`boundedCodeTraces (lockContentionAlphabet maxDelay) n`, a set of exactly
`lockContentionAlphabet maxDelay ^ n` elements — and by the pacing bound above,
`n` is itself bounded by the execution's length.

`lockContentionCode_injective` is what makes this a bound on the *channel*
rather than on an encoding of it: distinct codes are distinct observations, so
the count counts behaviours the contending core can actually tell apart.

Deliberately the same three-part shape as CC-1's treatment — alphabet, pacing,
trace capacity — so a reader comparing the SMP kernel's two accepted timing
channels is comparing like with like. -/
theorem lockContentionChannel_trace_capacity (maxDelay : Nat)
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (enqueueSteps : List Nat)
    (hRun : lockContentionRun maxDelay e c enqueueSteps) :
    lockContentionTrace e c enqueueSteps
      ∈ boundedCodeTraces (lockContentionAlphabet maxDelay) enqueueSteps.length := by
  obtain ⟨hFair, hInit, _, hSteps⟩ := hRun
  refine (mem_boundedCodeTraces _ _ _).mpr ⟨by simp [lockContentionTrace], ?_⟩
  intro x hx
  simp only [lockContentionTrace, List.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨⟨_, m, hQueued, _⟩, hWithin, hNoCancel⟩ := hSteps k hk
  exact lockContentionChannel_alphabet_bounded e maxDelay hFair hInit c m k hQueued hWithin
    hNoCancel

/-- SM8.D.3 (**the composed per-execution bound**): from a run alone — no extra
hypotheses — the core's trace is one of `alphabet ^ n` **and** `n` is at most the
execution's length.

`lockContentionChannel_trace_capacity` bounds the alphabet per position and
`lockContentionChannel_observation_rate_bounded` bounds the number of positions,
but the second needs the steps to be distinct.  Before that conjunct lived in
`lockContentionRun`, this composition did not typecheck from a run alone, and the
capacity docstring's "and by the pacing bound above, `n` is itself bounded by the
execution's length" was a claim about *some* runs rather than every accepted one.
Stating it as one theorem is what keeps the two halves from drifting apart
again. -/
theorem lockContentionChannel_run_capacity (maxDelay : Nat)
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (enqueueSteps : List Nat)
    (hRun : lockContentionRun maxDelay e c enqueueSteps) :
    lockContentionTrace e c enqueueSteps
        ∈ boundedCodeTraces (lockContentionAlphabet maxDelay) enqueueSteps.length ∧
      (lockContentionTrace e c enqueueSteps).length ≤ e.ops.length + 1 := by
  refine ⟨lockContentionChannel_trace_capacity maxDelay e c enqueueSteps hRun, ?_⟩
  obtain ⟨_, _, hNodup, hSteps⟩ := hRun
  refine lockContentionChannel_observation_rate_bounded e c enqueueSteps hNodup ?_
  intro k hk
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right k _) (hSteps k hk).2.1)

/-- SM8.D.3 (**the load-bearing negative**): a list that repeats a queued step is
**not** an accepted run, however well-behaved the execution is.

This is the shape the `Nodup` conjunct exists to exclude: repeating one
acquisition inflates `enqueueSteps.length` without the core making any further
observation, so a capacity figure computed from it would count the same
behaviour twice. -/
theorem lockContentionRun_rejects_repeated_step (maxDelay : Nat)
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (k : Nat)
    (rest : List Nat) (hMem : k ∈ rest) :
    ¬ lockContentionRun maxDelay e c (k :: rest) := by
  rintro ⟨_, _, hNodup, _⟩
  exact (List.nodup_cons.mp hNodup).1 hMem

/-- SM8.D.3 (**the second load-bearing negative**): a step at which the core was
*already* queued is not an accepted run entry, even though it is a step at which
the core is queued.

This is the shape `Nodup` alone could not exclude: a single acquisition that
waits across several steps would otherwise contribute one entry per step, each
with a different delay and therefore a different code, inflating the run length
without the core having started a second acquisition. -/
theorem lockContentionRun_rejects_still_queued_step (maxDelay : Nat)
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (k : Nat)
    (rest : List Nat)
    (hStill : ∀ m : AccessMode, (c, m) ∈ (e.stateAt k).waiters →
      (c, m) ∈ (e.stateAt (k - 1)).waiters) :
    ¬ lockContentionRun maxDelay e c (k :: rest) := by
  rintro ⟨_, _, _, hSteps⟩
  obtain ⟨⟨_, m, hIn, hOut⟩, _⟩ := hSteps k List.mem_cons_self
  exact hOut (hStill m hIn)

/-- SM8.D.3: and the run's entries really are acquisitions the core *started* —
each names a step at which it was not queued a moment earlier. -/
theorem lockContentionRun_steps_are_edges (maxDelay : Nat)
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (enqueueSteps : List Nat)
    (hRun : lockContentionRun maxDelay e c enqueueSteps) :
    ∀ k ∈ enqueueSteps, ∃ m : AccessMode,
      (c, m) ∈ (e.stateAt k).waiters ∧ (c, m) ∉ (e.stateAt (k - 1)).waiters := by
  obtain ⟨_, _, _, hSteps⟩ := hRun
  intro k hk
  obtain ⟨⟨_, m, hIn, hOut⟩, _⟩ := hSteps k hk
  exact ⟨m, hIn, hOut⟩

/-- SM8.D.3: and the count itself. -/
theorem lockContentionChannel_trace_count (maxDelay n : Nat) :
    (boundedCodeTraces (lockContentionAlphabet maxDelay) n).length
      = lockContentionAlphabet maxDelay ^ n :=
  boundedCodeTraces_length _ n

-- ----------------------------------------------------------------------------
-- SM8.D.3 — CC-5's inventory entry, now carrying a bound
-- ----------------------------------------------------------------------------

/-- SM8.D.3 (**the inventory tie-in**): CC-5 is registered `modelVisible := false`
with `severity := .medium`, and SM8.D supplies what the SM8.B entry could only
describe — the quantity behind the severity.

The three conjuncts are the entry's own literals and §3's bound, stated
together so a reclassification of CC-5 that is not matched by a change to the
bound breaks this theorem rather than passing silently.  This is the same
discipline `acceptedCovertChannel_lockContention_is_timing_only` applies to the
entry's `modelVisible` flag, extended to the figure the mitigation argument
rests on.

**Why it is a separate theorem rather than an arm of SM8.B's
`CovertChannelId.evidenceProp`** — which is the device that makes a mis-mapped
channel a *type* error rather than a stale string: that device lives in
`CovertChannelPerCore.lean`, which this module imports, so the dependency runs
the wrong way.  The equivalent protection here is `FineLockClaimId`'s
`.contentionChannelRegistered` arm, whose `evidenceProp` reads the entry's
literals off `acceptedCovertChannel_lockContention` directly. -/
theorem acceptedCovertChannel_lockContention_bounded (maxDelay : Nat)
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (m : AccessMode) (kEnq : Nat)
    (hQueued : (c, m) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length)
    (hNoCancel : e.noCancelIn c kEnq (kEnq + lockContentionDelayBound maxDelay + 1)) :
    acceptedCovertChannel_lockContention.modelVisible = false ∧
      acceptedCovertChannel_lockContention.severity = .medium ∧
      lockContentionCode e c kEnq < lockContentionAlphabet maxDelay :=
  ⟨rfl, rfl,
   lockContentionChannel_alphabet_bounded e maxDelay hFair hInit c m kEnq hQueued hWithin
     hNoCancel⟩

/-- SM8.D.3 (**what the severity is a judgement about**): CC-5's `.medium` is
not derived from the bound — a severity is an engineering judgement, and
deriving one from a number would be dressing it up.  What SM8.D supplies is the
set of quantitative facts the judgement now rests on, pinned here so that a
future re-grading is a re-reading of *these* rather than of prose:

* the per-observation alphabet is **bounded** — the channel is not unbounded;
* the channel is **not closed** — and that conjunct is the *reachability*
  witness, not the alphabet's arithmetic floor.  An allocated code is not a
  producible one: under the premises an accepted run carries, the two codes the
  floor counts are precisely the two such a run cannot produce
  (`acceptedContentionCode_ge_two`).  So the grading rests on two fair,
  in-premise executions whose contending cores read *different* codes — and it
  carries **the fairness and enqueue-edge premises themselves**, not merely the
  resulting inequality.  Two distinct codes read off executions that are no
  longer fair, no longer genuine enqueue edges, or no longer long enough for the
  delay bound would say nothing about *accepted* runs; with the premises inlined
  here, a fixture drifting out of them breaks this theorem rather than quietly
  leaving the grading resting on observations no run can make;
* the alphabet is `(numCores - 1) × (maxDelay + 1) + 2`, so it grows with the
  core count and the critical-section budget and with nothing else;
* the channel has **one instance per core**, so a deployment's exposure scales
  with `numCores` as well.

Compare CC-1, whose `.medium` rests on an alphabet *and* a tick-paced rate; CC-5
now has both (`lockContentionChannel_observation_rate_bounded`), which is what
makes the two gradings comparable. -/
theorem acceptedCovertChannel_lockContention_severity_basis (maxDelay : Nat) :
    acceptedCovertChannel_lockContention.severity = .medium ∧
      acceptedCovertChannel_lockContention.perCoreInstance = true ∧
      2 ≤ lockContentionAlphabet maxDelay ∧
      lockContentionAlphabet maxDelay = (numCores - 1) * (maxDelay + 1) + 2 ∧
      -- The **non-closure** half of the grading, carrying the premises that make
      -- the two observations accepted ones.  The raw code inequality alone is
      -- not enough: a fixture that stopped being fair, stopped being a genuine
      -- enqueue edge, or became too short for the delay bound would still have
      -- distinct codes, and this theorem would keep elaborating while the
      -- executions behind it no longer satisfied anything a run imposes.
      SeLe4n.Kernel.Concurrency.FairTrace singleWaiterExecution 2 ∧
      SeLe4n.Kernel.Concurrency.FairTrace twoWaiterExecution 2 ∧
      ((waiterCore, AccessMode.write) ∈ (singleWaiterExecution.stateAt 2).waiters ∧
        (waiterCore, AccessMode.write) ∉ (singleWaiterExecution.stateAt 1).waiters ∧
        2 + lockContentionDelayBound 2 < singleWaiterExecution.ops.length) ∧
      ((waiterCore, AccessMode.write) ∈ (twoWaiterExecution.stateAt 3).waiters ∧
        (waiterCore, AccessMode.write) ∉ (twoWaiterExecution.stateAt 2).waiters ∧
        3 + lockContentionDelayBound 2 < twoWaiterExecution.ops.length) ∧
      lockContentionCode singleWaiterExecution waiterCore 2
        ≠ lockContentionCode twoWaiterExecution waiterCore 3 ∧
      -- The **rate** half of the grading, in elapsed time rather than lock
      -- operations.  Consumed here rather than merely proven nearby: without
      -- this conjunct the elapsed-time result could be deleted while the
      -- severity justification — which reads as a bandwidth argument — kept
      -- elaborating on the operation-count bound alone.
      -- WS-LC LC5.8: at the execution's own cost model, for the reason the
      -- registration arm gives.
      (∀ (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (tMin : Nat),
        e.CostedCriticalSection tMin → ∀ steps : List Nat, steps.Nodup →
        (∀ k ∈ steps, k ≤ e.ops.length) → (∀ k ∈ steps, 1 ≤ k) →
        steps.length * tMin ≤ e.elapsed 0 e.ops.length) :=
  ⟨rfl, rfl, lockContentionAlphabet_at_least_two maxDelay, rfl,
   contentionWitnesses_fair.1, contentionWitnesses_fair.2,
   contentionWitnesses_in_premises.1, contentionWitnesses_in_premises.2,
   lockContentionChannel_two_codes_reachable.2.2,
   fun e tMin hCost steps hNodup hRange hPos =>
     lockContentionChannel_rate_per_execution_time e tMin hCost steps hNodup hRange hPos⟩

-- ============================================================================
-- §4  SM8.D.4 — Biba integrity under per-core locks
-- ============================================================================
--
-- Integrity asks which *subjects* may modify which *objects*.  Until WS-LS
-- LS3.1 fine-grained locking made every core a writer of every object it
-- touched — an acquire was a store into that object's lock word — and §4 had
-- to argue that the write was not one an integrity policy governs.  The lock
-- state is now the ghost table beside the kernel state, so an acquire writes
-- **no object at all**, and the question the plan's D.4 row raised dissolves:
-- the 2PL bracket's only kernel-state writes are its guarded action's.
--
-- What §4 still has to say is stated in a form that does not depend on which
-- direction the deployment's integrity order runs.  seLe4n's `integrityFlowsTo`
-- is deliberately the *reverse* of standard BIBA (U6-I: the dimension tracks
-- authority delegation, not data purity), and `bibaIntegrityFlowsTo` is the
-- standard order kept as a drop-in.  A result about only one of them would say
-- nothing about a deployment configured with the other, so §4 is stated over an
-- arbitrary write rule and instantiated at both.
--
-- One subtlety worth stating rather than leaving to be noticed.  *Which* keys a
-- subject causes to be acquired is a function of the lock set, and the lock set
-- is a function of the syscall the subject issued.  So the choice of footprint
-- is subject-influenced.  That does not open an integrity flow: the table is
-- read by no observer (§1) and no integrity predicate.  What the choice *can*
-- affect is how long another core spins, and that is CC-5 — bounded in §3, and
-- a timing channel rather than an integrity violation.

/-- SM8.D.4: the standard-BIBA write rule — a subject may modify an object only
if the object's integrity is no greater than the subject's (no write-up).

The argument order is the one `securityFlowsTo` uses: a flow `src → dst`
checks `integrityFlowsTo dst.integrity src.integrity`, so a *write into* `oid`
by `subject` checks the object's integrity against the subject's. -/
def bibaWritePermitted (ctx : LabelingContext) (subject : SecurityLabel)
    (oid : SeLe4n.ObjId) : Bool :=
  bibaIntegrityFlowsTo (ctx.objectLabelOf oid).integrity subject.integrity

/-- SM8.D.4: seLe4n's own (authority-flow) write rule, in the same position —
`integrityFlowsTo`, which admits untrusted → trusted and denies trusted →
untrusted, the deliberate reversal U6-I documents. -/
def authorityWritePermitted (ctx : LabelingContext) (subject : SecurityLabel)
    (oid : SeLe4n.ObjId) : Bool :=
  integrityFlowsTo (ctx.objectLabelOf oid).integrity subject.integrity

/-- SM8.D.4: **the two rules are genuinely different**, so §4's two
instantiations are two results and not one restated.

Witness: an all-trusted object labelling with an untrusted subject.  Standard
BIBA forbids the write (no write-up); seLe4n's authority direction permits it
(authority receipt).  This is `integrityFlowsTo_is_not_biba` lifted to the write
rules the section is stated over. -/
def writeRulesWitnessContext : LabelingContext :=
  { objectLabelOf := fun _ => SecurityLabel.kernelTrusted
    threadLabelOf := fun tid =>
      if tid = (⟨0⟩ : SeLe4n.ThreadId) then SecurityLabel.kernelTrusted
      else SecurityLabel.publicLabel
    endpointLabelOf := fun _ => SecurityLabel.publicLabel
    serviceLabelOf := fun _ => SecurityLabel.publicLabel }

/-- SM8.D.4: the witness context is **not** the degenerate all-public labelling.

AK6-H's `labelNonTriviality` exists because a context that assigns one label to
everything makes every flow trivially permitted and every information-flow
witness vacuous.  This one differentiates two threads, so the disagreement below
is exhibited on a labelling a deployment could hold rather than on the one the
deployment gate rejects. -/
theorem writeRulesWitnessContext_nontrivial :
    ∃ tid₁ tid₂ : SeLe4n.ThreadId,
      writeRulesWitnessContext.threadLabelOf tid₁
        ≠ writeRulesWitnessContext.threadLabelOf tid₂ :=
  ⟨⟨0⟩, ⟨1⟩, by decide⟩

theorem writeRules_differ :
    ∃ (ctx : LabelingContext) (subject : SecurityLabel) (oid : SeLe4n.ObjId),
      bibaWritePermitted ctx subject oid ≠ authorityWritePermitted ctx subject oid :=
  ⟨writeRulesWitnessContext, SecurityLabel.publicLabel, ⟨0⟩, by decide⟩

/-- SM8.D.4: **a step performs no write the rule `permitted` forbids** — every
object the rule denies comes out of the step with its stored value unchanged.

Raw object equality, with no erasure: since WS-LS LS3.1 no lock state lives in
an object, so the predicate that used to read "unchanged modulo lock words" is
now standard no-write-up over the stored objects themselves.  (The lock-erased
form and the two theorems that justified it, `lockWrite_carries_no_subject_data`
and `lockAcquisition_modifies_trusted_object_and_is_not_counted`, went with the
lock words; this form is strictly stronger.)

What is **not** claimed: that lock acquisition cannot be used to delay a trusted
subject.  It can, and that is CC-5's subject. -/
def noUnpermittedWrite (permitted : SeLe4n.ObjId → Bool) (s s' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, permitted oid = false → s'.objects[oid]? = s.objects[oid]?

theorem noUnpermittedWrite_refl (permitted : SeLe4n.ObjId → Bool) (s : SystemState) :
    noUnpermittedWrite permitted s s := fun _ _ => rfl

theorem noUnpermittedWrite_trans {permitted : SeLe4n.ObjId → Bool} {s₁ s₂ s₃ : SystemState}
    (h₁ : noUnpermittedWrite permitted s₁ s₂) (h₂ : noUnpermittedWrite permitted s₂ s₃) :
    noUnpermittedWrite permitted s₁ s₃ :=
  fun oid hDenied => (h₂ oid hDenied).trans (h₁ oid hDenied)

/-- SM8.D.4: **a lock-only step satisfies every write rule at once.**  No
hypothesis on the rule, on the subject, on the labelling, or on which keys the
lock set names. -/
theorem lockWritesOnly_noUnpermittedWrite (permitted : SeLe4n.ObjId → Bool)
    {s s' : LockedSystemState} (h : lockWritesOnly s s') :
    noUnpermittedWrite permitted s.kernel s'.kernel :=
  fun _ _ => by rw [h]

-- ----------------------------------------------------------------------------
-- SM8.D.4 — the bracket, under an arbitrary write rule and then at both
-- ----------------------------------------------------------------------------

/-- SM8.D.4 (**the generic result**): a 2PL bracket performs no write the rule
forbids, whenever its guarded action performs none — for *any* write rule, and
for *any* acquiring core.

The genericity is the content, not convenience: it is what makes the two
instantiations below cover a deployment configured either way round, and what
makes the result independent of the labelling entirely. -/
theorem withLockSet_noUnpermittedWrite {α : Type} (permitted : SeLe4n.ObjId → Bool)
    (S : LockSet) (core : CoreId) (action : SystemState → SystemState × α)
    (s : LockedSystemState)
    (hAction : noUnpermittedWrite permitted s.kernel (action s.kernel).1) :
    noUnpermittedWrite permitted s.kernel
      (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1.kernel :=
  hAction

/-- SM8.D.4 (**the headline, standard BIBA**): under per-core locks, a subject
at integrity `subject.integrity` running on **any** core writes no object
standard BIBA forbids it to write, whenever the transition it brackets writes
none.  Acquiring a lock on a trusted object from an untrusted core writes the
ghost table, not the object. -/
theorem bibaIntegrity_underLockSet {α : Type} (ctx : LabelingContext) (subject : SecurityLabel)
    (S : LockSet) (core : CoreId) (action : SystemState → SystemState × α)
    (s : LockedSystemState)
    (hAction : noUnpermittedWrite (bibaWritePermitted ctx subject) s.kernel (action s.kernel).1) :
    noUnpermittedWrite (bibaWritePermitted ctx subject) s.kernel
      (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1.kernel :=
  withLockSet_noUnpermittedWrite _ S core action s hAction

/-- SM8.D.4 (**the headline, seLe4n's authority direction**): the same, for the
integrity order the kernel actually ships with. -/
theorem authorityIntegrity_underLockSet {α : Type} (ctx : LabelingContext)
    (subject : SecurityLabel) (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState)
    (hAction :
      noUnpermittedWrite (authorityWritePermitted ctx subject) s.kernel (action s.kernel).1) :
    noUnpermittedWrite (authorityWritePermitted ctx subject) s.kernel
      (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1.kernel :=
  withLockSet_noUnpermittedWrite _ S core action s hAction

/-- SM8.D.4 (**"under per-core locks"**, spelled out): the acquire and release
phases satisfy both integrity rules on *every* core, with no hypothesis on the
guarded action at all — because those phases write only the ghost table.

The `∀ core` is what makes this a statement about per-core locking rather than
about one core's bracket: whichever core takes the set, and however many take
sets concurrently (`noUnpermittedWrite_trans` composes their steps), the lock
traffic itself adds no integrity-relevant write. -/
theorem lockPhases_integrity_clean_on_every_core (ctx : LabelingContext)
    (subject : SecurityLabel) (S : LockSet) (s : LockedSystemState) :
    ∀ core : CoreId,
      noUnpermittedWrite (bibaWritePermitted ctx subject) s.kernel
        { s with locks := LockState.acquireAll core S.lockAcquireSequence s.locks }.kernel ∧
      noUnpermittedWrite (authorityWritePermitted ctx subject) s.kernel
        { s with locks := LockState.acquireAll core S.lockAcquireSequence s.locks }.kernel ∧
      noUnpermittedWrite (bibaWritePermitted ctx subject) s.kernel
        { s with locks := LockState.unwindAll core S.lockAcquireSequence.reverse s.locks }.kernel ∧
      noUnpermittedWrite (authorityWritePermitted ctx subject) s.kernel
        { s with locks := LockState.unwindAll core S.lockAcquireSequence.reverse s.locks }.kernel :=
  fun _ =>
    ⟨lockWritesOnly_noUnpermittedWrite _ (lockTableWrite_lockWritesOnly s _),
     lockWritesOnly_noUnpermittedWrite _ (lockTableWrite_lockWritesOnly s _),
     lockWritesOnly_noUnpermittedWrite _ (lockTableWrite_lockWritesOnly s _),
     lockWritesOnly_noUnpermittedWrite _ (lockTableWrite_lockWritesOnly s _)⟩

-- ============================================================================
-- §5  SM8.D.5 — the secure-information-flow witness under fine locks
-- ============================================================================
--
-- The *shape* of a bracketed entry is fixed by `lockSetForSyscall`: resolve
-- the syscall's declared footprint from the pre-state, bracket the entry in
-- it, commit.  §5 states the information-flow property of exactly
-- that shape, so the migration inherits its security argument instead of
-- needing a new one.
--
-- Two things are worth reading closely.
--
-- First, `commitKernelAction`: `withLockSet` brackets a *total* state
-- transformer, and a kernel entry is a partial one, so the adapter has to say
-- what a failure commits.  It commits the pre-state — which is what the runtime
-- does, and what makes the fail-closed statement below true.
--
-- Second, the fail-closed statement keeps its strongest form.  Unbracketed, a
-- denied syscall leaves the state *identical* (`…_denied_preserves_state`).
-- Bracketed, the growing and shrinking phases advance the ghost lock table, and
-- the kernel half is still identical — the denied entry commits its input and
-- the phases write only `locks` — so the fail-closed theorems below conclude
-- kernel-half equality, not merely invisibility.

/-- SM8.D.5: a `Kernel` action as the total state transformer the 2PL bracket
takes — commit the post-state on success, keep the pre-state on failure.

This is the runtime's own convention (`Platform.FFI`'s commit seam installs the
post-state only for `.ok`), lifted so the bracket and the entry compose. -/
def commitKernelAction {α : Type} (k : Kernel α) (s : SystemState) :
    SystemState × Except KernelError α :=
  match k s with
  | .ok (a, s') => (s', .ok a)
  | .error e => (s, .error e)

@[simp] theorem commitKernelAction_ok {α : Type} (k : Kernel α) (s s' : SystemState) (a : α)
    (h : k s = .ok (a, s')) : commitKernelAction k s = (s', .ok a) := by
  unfold commitKernelAction; rw [h]

@[simp] theorem commitKernelAction_error {α : Type} (k : Kernel α) (s : SystemState)
    (e : KernelError) (h : k s = .error e) : commitKernelAction k s = (s, .error e) := by
  unfold commitKernelAction; rw [h]

/-- SM8.D.5 (**the missing per-core live-entry witness**): the
information-flow-checked syscall entry preserves the observer's projection when
the operation it dispatches does.

SM8.B.12 stated this for `syscallEntry`, the boot-pinned pre-SMP entry, because
that is where the release-grade witness lived; the entry the SMP dispatch seam
actually calls is `syscallEntryChecked`, and it had none.  The three steps
before the dispatch are the same as the unchecked entry's — the context check
is state-free, the register lookup is read-only, the decode is pure — plus the
SM7.F.5 access-time TLB fill, which writes `perCoreTlb` and nothing else
(`tlbFillIpcBufferOnCore_eq_setPerCoreTlb`) and is invisible by
`perCoreTlb_write_preserves_projection`.

The dispatch hypothesis is stated against the **filled** state, because that is
the state `dispatchSyscallChecked` is applied to. -/
theorem syscallEntryChecked_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (st st' : SystemState)
    (hOk : syscallEntryChecked ctx layout executingCore regCount st = .ok ((), st'))
    (hDispatchProj : ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
        (stPost : SystemState),
        dispatchSyscallChecked ctx decoded tid executingCore
            (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
              decoded.overflowCount) = .ok ((), stPost) →
        projectState ctx observer stPost
          = projectState ctx observer
              (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                decoded.overflowCount)) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold syscallEntryChecked at hOk
  split at hOk
  · exact absurd hOk (by simp)
  · split at hOk
    · exact absurd hOk (by simp)
    · next tid _ =>
      split at hOk
      · exact absurd hOk (by simp)
      · next regsPair _ =>
        obtain ⟨regs, _⟩ := regsPair
        split at hOk
        · exact absurd hOk (by simp)
        · next decoded _ =>
          -- PR #873 round 6: the taint seam moved into `dispatchSyscallChecked`,
          -- so the entry delegates and `hOk` IS the dispatch's own success.  The
          -- seam is still projection-invisible
          -- (`applySyscallTaint_preserves_projection`, `rfl`), which is what lets
          -- `hDispatchProj` be discharged from a statement about the arm.
          --
          -- The entry binds the TLB-filled state once rather than spelling it out
          -- three times; Lean elaborates that binding to `letFun`, which the
          -- rewrite below cannot see through, so reduce it away first.
          dsimp only at hOk
          rw [hDispatchProj decoded tid st' hOk]
          obtain ⟨t, hEq⟩ :=
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb st executingCore tid
              decoded.overflowCount
          rw [hEq]
          exact perCoreTlb_write_preserves_projection ctx observer st t

-- ============================================================================
-- §4b  WS-SM SM9.D.18 — the taint propagation carries the non-interference
-- ============================================================================

/-- WS-SM SM9.D.18: **the propagation writes no core's observable slots.**

`applySyscallTaint` changes exactly one `SystemState` field, and that field is
in none of the six per-core components `observableSlotsConfinedToCores` reads —
no run queue, no current slot, no domain state, no register bank.  So it is
confined to the **empty** set of cores, which is the sharpest statement
available and the one the cross-core inventory composes with: a content-moving
arm's write set is exactly the transition's, unchanged by the propagation the
entry runs on top of it. -/
theorem applySyscallTaint_confinedToCores_nil (plan : TaintPlan) (pre post : SystemState) :
    observableSlotsConfinedToCores post (applySyscallTaint plan pre post) [] :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   fun _ _ => rfl⟩

/-- WS-SM SM9.D.18 / SM9.D.6: **the propagation is invisible on every core.**

The per-core companion of `applySyscallTaint_preserves_projection`.  Both halves
are needed and neither implies the other: being outside the projection says the
write moves no observer's global view, and being outside the per-core read set
says the same on a core other than the one the propagating syscall executed on —
which is the statement the cross-core non-interference inventory consumes, since
every content-moving arm can run on any core. -/
theorem applySyscallTaint_preserves_onCore (ctx : LabelingContext) (L : SecurityLabel)
    (c : CoreId) (plan : TaintPlan) (pre post : SystemState) :
    ObservableState.onCore ctx c L (applySyscallTaint plan pre post)
      = ObservableState.onCore ctx c L post :=
  onCore_declassificationTaint ctx L post c _

/-- WS-SM SM9.D.18: **the whole invariant bundle across the propagation.**

Unconditional, because no `proofLayerInvariantBundle` conjunct reads the taint
table — each entry is bounded by its own type, so a writer owes nothing to the
sixteen conjuncts that are already there.  This is the carriage the mount
checklist's step 8 requires of *every* mounted field, and it is what a
whole-entry bundle-preservation proof for the live path composes with. -/
theorem applySyscallTaint_preserves_proofLayerInvariantBundle (plan : TaintPlan)
    (pre post : SystemState) (h : Architecture.proofLayerInvariantBundle post) :
    Architecture.proofLayerInvariantBundle (applySyscallTaint plan pre post) :=
  Architecture.proofLayerInvariantBundle_setDeclassificationTaint post _ h

/-- SM8.D.5 (**WS-LS LS2.1**: over the pair): **the 2PL-bracketed live syscall
entry** — the shape SM3.C.9 installs at the `@[export]` bodies: take the
declared footprint in the executing core's name, run the
information-flow-checked entry, release.

**What the bracket does and does not provide.**  The bracket is
`withLockSet` over `LockedSystemState`: the growing phase writes the
**ghost lock table** (`s.locks`, by `LockState.bracket`) and the entry runs on
the **kernel half** (`s.kernel`), so by type the lock trace never touches a
kernel object.  The growing phase folds SM2.C's `tryAcquire*`, which
*enqueues* a core when the lock is already held rather than granting it, and
the bracket runs its action regardless — a pure total state transformer has no
way to block.  So the growing phase declares a footprint and advances the
table; it does **not** by itself establish mutual exclusion.  Exclusion is the
bracket's **guard** (`BracketSpec.guard`): established under the entry lock by
`BracketSpec.guard_of_unheld`, and refuted under contention by its
load-bearing negative `BracketSpec.not_guard_of_contended` (the ghost forms
of this file's former `lockSetAcquiredState_grants_when_free` and
`lockSetAcquiredState_does_not_grant_when_contended`, retired by LS2.1).

The §5 results do not rest on exclusion: they are statements about the kernel
half, which the lock phases do not touch, so they hold whether the acquisition
granted or queued — which is precisely why the SM3.C.9 migration is a change of
concurrency control and not of the security argument.  Before LS2.1 the phases
wrote lock words into kernel objects and every §5 theorem carried an `invExt`
guard so that §1 could show those writes invisible; over the pair the kernel
half of the result *is* the entry's (`syscallEntryUnderLockSet_fst`, `rfl`),
and those guards are gone.  Live exclusion today comes from the SM5.I global
kernel-entry ticket lock, not from this bracket.

`lockCore` and `executingCore` are separate parameters on purpose.  They are
the same core on the live path (the trapping core takes the locks its own
syscall needs), but nothing in the information-flow argument requires it, and
tying them here would hide that the §5 results hold for any pairing — including
the migration's intermediate states, where a coarser bracket may be taken by
one core on behalf of a transition attributed to another. -/
def syscallEntryUnderLockSet (ctx : LabelingContext) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SeLe4n.Kernel.Concurrency.LockedSystemState) :
    SeLe4n.Kernel.Concurrency.LockedSystemState × Except KernelError Unit :=
  SeLe4n.Kernel.Concurrency.withLockSet S lockCore
    (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)) s

/-- SM8.D.5 (**WS-LS LS2.1**): the kernel half of the bracket's result is the
committed entry at `s.kernel` — the state the growing phase hands the entry
**is** the kernel half it was given, because the growing phase writes only the
table.  Before LS2.1 this exposed the three word-level phases
(`unwindAll … (commitKernelAction … (acquireAll … s)).1`); over the pair the
lock trace sits in `.locks` (`withLockSet_fst_locks`) and this is `rfl`.
The value half is `withLockSet_snd`. -/
theorem syscallEntryUnderLockSet_fst (ctx : LabelingContext) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SeLe4n.Kernel.Concurrency.LockedSystemState) :
    (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel
      = (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)
          s.kernel).1 :=
  SeLe4n.Kernel.Concurrency.withLockSet_fst_kernel _ _ _ _

/-- SM8.D.5 (**the headline, at the core the entry runs on**): a 2PL-bracketed
live syscall entry is non-interfering on **every core** exactly when the
operation it dispatches is confined to the core it runs on.

The confinement core is a **parameter**, and that matters rather than being
generality for its own sake.  The boot-core form below is the instance a
whole-projection hypothesis can feed, because `projectState` *is* the boot core's
view — but an ordinary SMP syscall executes on a secondary core and writes *that*
core's scheduler slots, which makes boot-core confinement false and the boot form
vacuous for it.  Pinned there, "non-interfering on every core" would be a
conclusion about transitions the live SMP path does not take.

The bracket itself contributes nothing at any core: its growing and shrinking
phases write the ghost table and the kernel half is the entry's own output
(`syscallEntryUnderLockSet_fst`).  So the SM3.C.9 migration does not weaken the
information-flow guarantee — the hypotheses are exactly the ones the
*unbracketed* per-core statement takes, at the kernel half the entry is run on.

**WS-LS LS2.1 (strengthened).**  Dropped `hInv : s.objects.invExt` and
`hOutInv : st'.objects.invExt`: both existed only so that §1 could show the
word-level lock writes of the growing and shrinking phases invisible
(`acquireAll_lockWritesOnly`, `unwindAll_lockWritesOnly`); over the pair there
are no such writes. -/
theorem syscallEntryUnderLockSet_preserves_projectionOnCore_atCore (ctx : LabelingContext)
    (observer : IfObserver) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (st' : SystemState) (c' : CoreId)
    (hOk : syscallEntryChecked ctx layout executingCore regCount s.kernel = .ok ((), st'))
    (hProjOn : projectStateOnCore ctx observer st' c'
        = projectStateOnCore ctx observer s.kernel c')
    (hConfined : observableSlotsConfinedToCore s.kernel st' c') :
    lowEquivalent_smp ctx observer
      (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel
      s.kernel := by
  rw [syscallEntryUnderLockSet_fst, commitKernelAction_ok _ _ _ _ hOk]
  exact lowEquivalent_smp_of_projectionOnCore_and_confinement ctx observer
    (c' := c') hProjOn hConfined

/-- SM8.D.5 (**the headline**): a 2PL-bracketed live syscall entry is
non-interfering on **every core** exactly when the operation it dispatches is.

The boot-core instance of `…_atCore`: `projectState` is the boot core's view, so
a whole-projection hypothesis discharges the per-core premise there and nowhere
else.  Kept as its own statement because it is the form the boot-pinned
`syscallEntryChecked_preserves_projection` feeds directly.

**WS-LS LS2.1 (strengthened).**  Over the pair; dropped `hInv` and `hOutInv`
(the word-level lock-write invisibility guards) as in `…_atCore`. -/
theorem syscallEntryUnderLockSet_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (st' : SystemState)
    (hOk : syscallEntryChecked ctx layout executingCore regCount s.kernel = .ok ((), st'))
    (hDispatchProj : ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
        (stPost : SystemState),
        dispatchSyscallChecked ctx decoded tid executingCore
            (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
              s.kernel executingCore tid decoded.overflowCount)
              = .ok ((), stPost) →
        projectState ctx observer stPost
          = projectState ctx observer
              (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
                s.kernel executingCore tid decoded.overflowCount))
    (hConfined : observableSlotsConfinedToCore s.kernel st' bootCoreId) :
    lowEquivalent_smp ctx observer
      (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel
      s.kernel := by
  refine syscallEntryUnderLockSet_preserves_projectionOnCore_atCore ctx observer S lockCore
    layout executingCore regCount s st' bootCoreId hOk ?_ hConfined
  rw [projectStateOnCore_bootCore, projectStateOnCore_bootCore]
  exact syscallEntryChecked_preserves_projection ctx observer layout executingCore regCount
    _ st' hOk hDispatchProj

/-- SM8.D.5 (**fail-closed, sharpened**; **WS-LS LS2.1**: over the pair): a
refused syscall under fine locks moves the ghost lock table and **nothing
else** — the kernel half comes back *identical*, and the refusal is reported
unchanged through the bracket.

The unbracketed fail-closed theorems (`…_denied_preserves_state`) conclude the
state is identical.  Before LS2.1 that claim did not survive the bracket,
because the growing and shrinking phases wrote real lock words into kernel
objects (`KernelObject.updateLock_not_identity`), and what survived was the
weaker `lockWritesOnly`.  Over the pair the lock trace lives in `.locks`
(`withLockSet_fst_locks`) and the kernel half is the committed entry's
input (`commitKernelAction_error`), so the identity is recovered on the kernel
half — which is what the result is stated as, never as an identity of the
whole pair: the table moved (`LockState.bracket`), and a refusal must still
be a bracket.

**WS-LS LS2.1 (strengthened).**  The first conjunct is sharpened from
`lockWritesOnly s …` to kernel-half equality, and `hInv : s.objects.invExt`
(the word-level lock-write invisibility guard) is dropped. -/
theorem syscallEntryUnderLockSet_failClosed (ctx : LabelingContext) (S : LockSet)
    (lockCore : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId)
    (regCount : Nat) (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (e : KernelError)
    (hDenied : syscallEntryChecked ctx layout executingCore regCount s.kernel = .error e) :
    (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel
        = s.kernel
      ∧ (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).2
          = .error e := by
  have hCommit : (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)
      s.kernel) = (s.kernel, .error e) :=
    commitKernelAction_error _ _ _ hDenied
  constructor
  · rw [syscallEntryUnderLockSet_fst, hCommit]
  · show (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)
      s.kernel).2 = _
    rw [hCommit]

/-- SM8.D.5: and therefore a refused syscall is invisible to every observer on
every core — the guarantee the literal state equality was standing in for.
Before LS2.1 this was recovered from the weaker `lockWritesOnly` conclusion by
§1; over the pair it is the kernel-half equality read through the observer.

**WS-LS LS2.1 (strengthened).**  Dropped `hInv : s.objects.invExt`. -/
theorem syscallEntryUnderLockSet_failClosed_invisible (ctx : LabelingContext) (S : LockSet)
    (lockCore : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId)
    (regCount : Nat) (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (e : KernelError)
    (L : SecurityLabel)
    (hDenied : syscallEntryChecked ctx layout executingCore regCount s.kernel = .error e) :
    ∀ c : CoreId,
      ObservableState.onCore ctx c L
          (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel
        = ObservableState.onCore ctx c L s.kernel :=
  fun c => by
    rw [(syscallEntryUnderLockSet_failClosed ctx S lockCore layout executingCore regCount s e
      hDenied).1]

/-- SM8.D.5 (**the witness**): *secure information flow under fine locks*, as
one statement.

For a 2PL-bracketed live syscall entry, on any pairing of lock-holding and
executing cores, and for a subject at any integrity:

1. **confidentiality** — the observer `(c, L)` sees the same state before and
   after, on **every** core;
2. **integrity, standard BIBA** — no object the subject may not write comes out
   with different content;
3. **integrity, seLe4n's authority direction** — likewise under the order the
   kernel ships with;
4. **the bracket's own contribution is nil** — the acquire and release phases
   add no write to (2) or (3) and no observation to (1): over the pair they
   write the ghost table alone (`syscallEntryUnderLockSet_fst`).

Every hypothesis is a property of the *guarded entry at the kernel half it is
run on*.  There is no hypothesis about the lock set — not about which objects
it names, not about whether those objects are observable, not about
contention — and that absence is the result: fine-grained locking is
information-flow transparent, so SM3.C.9's migration is a change of
concurrency control and not of the security argument.

**WS-LS LS2.1 (strengthened).**  Over the pair; dropped `hInv : s.objects.invExt`
and `hOutInv : st'.objects.invExt`, which existed only to carry (1)–(3)
across the word-level lock writes (`withLockSet_noUnpermittedWrite`, §1). -/
theorem secureInformationFlow_underFineLocks_atCore (ctx : LabelingContext) (L : SecurityLabel)
    (subject : SecurityLabel) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (st' : SystemState) (c' : CoreId)
    (hOk : syscallEntryChecked ctx layout executingCore regCount s.kernel = .ok ((), st'))
    (hProjOn : projectStateOnCore ctx (IfObserver.ofLabel L) st' c'
        = projectStateOnCore ctx (IfObserver.ofLabel L) s.kernel c')
    (hConfined : observableSlotsConfinedToCore s.kernel st' c')
    (hBiba : noUnpermittedWrite (bibaWritePermitted ctx subject) s.kernel st')
    (hAuthority : noUnpermittedWrite (authorityWritePermitted ctx subject) s.kernel st') :
    (∀ c : CoreId,
        ObservableState.onCore ctx c L
            (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel
          = ObservableState.onCore ctx c L s.kernel) ∧
      noUnpermittedWrite (bibaWritePermitted ctx subject) s.kernel
        (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel ∧
      noUnpermittedWrite (authorityWritePermitted ctx subject) s.kernel
        (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel := by
  have hCommit : (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)
      s.kernel) = (st', .ok ()) :=
    commitKernelAction_ok _ _ _ _ hOk
  refine ⟨syscallEntryUnderLockSet_preserves_projectionOnCore_atCore ctx (IfObserver.ofLabel L) S
    lockCore layout executingCore regCount s st' c' hOk hProjOn hConfined, ?_, ?_⟩
  <;> rw [syscallEntryUnderLockSet_fst, hCommit]
  · exact hBiba
  · exact hAuthority

/-- SM8.D.5: the boot-core instance of the combined witness.

Kept because a caller holding the boot-pinned whole-projection fact
(`syscallEntryChecked_preserves_projection`) can discharge its premise directly;
`…_atCore` is the form an ordinary SMP success path needs, since a syscall
executing on a secondary core writes that core's slots and cannot satisfy
boot-core confinement.

**WS-LS LS2.1 (strengthened).**  Over the pair; dropped `hInv` and `hOutInv`
as in `…_atCore`. -/
theorem secureInformationFlow_underFineLocks (ctx : LabelingContext) (L : SecurityLabel)
    (subject : SecurityLabel) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (st' : SystemState)
    (hOk : syscallEntryChecked ctx layout executingCore regCount s.kernel = .ok ((), st'))
    (hDispatchProj : ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
        (stPost : SystemState),
        dispatchSyscallChecked ctx decoded tid executingCore
            (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
              s.kernel executingCore tid decoded.overflowCount)
              = .ok ((), stPost) →
        projectState ctx (IfObserver.ofLabel L) stPost
          = projectState ctx (IfObserver.ofLabel L)
              (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
                s.kernel executingCore tid decoded.overflowCount))
    (hConfined : observableSlotsConfinedToCore s.kernel st' bootCoreId)
    (hBiba : noUnpermittedWrite (bibaWritePermitted ctx subject) s.kernel st')
    (hAuthority : noUnpermittedWrite (authorityWritePermitted ctx subject) s.kernel st') :
    (∀ c : CoreId,
        ObservableState.onCore ctx c L
            (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel
          = ObservableState.onCore ctx c L s.kernel) ∧
      noUnpermittedWrite (bibaWritePermitted ctx subject) s.kernel
        (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel ∧
      noUnpermittedWrite (authorityWritePermitted ctx subject) s.kernel
        (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel := by
  refine secureInformationFlow_underFineLocks_atCore ctx L subject S lockCore layout
    executingCore regCount s st' bootCoreId hOk ?_ hConfined hBiba hAuthority
  rw [projectStateOnCore_bootCore, projectStateOnCore_bootCore]
  exact syscallEntryChecked_preserves_projection ctx (IfObserver.ofLabel L) layout executingCore
    regCount _ st' hOk hDispatchProj

/-- SM8.D.5: the headline with the projection hypothesis stated at the **entry**
rather than at the dispatch — the form a caller in possession of a whole-entry
witness reaches for, and the one §6's evidence table is stated over.

Strictly the same result: `syscallEntryChecked_preserves_projection` is what
turns the dispatch-level hypothesis into this one, so having both is not
redundancy but the two places a caller's evidence can come from.

**WS-LS LS2.1 (strengthened).**  Over the pair; dropped `hInv` and `hOutInv`
(the word-level `acquireAll_preserves_projection` /
`unwindAll_preserves_projection` guards). -/
theorem syscallEntryUnderLockSet_preserves_projectionOnCore_of_entry (ctx : LabelingContext)
    (observer : IfObserver) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (st' : SystemState)
    (hOk : syscallEntryChecked ctx layout executingCore regCount s.kernel = .ok ((), st'))
    (hProj : projectState ctx observer st' = projectState ctx observer s.kernel)
    (hConfined : observableSlotsConfinedToCore s.kernel st' bootCoreId) :
    lowEquivalent_smp ctx observer
      (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel
      s.kernel := by
  rw [syscallEntryUnderLockSet_fst, commitKernelAction_ok _ _ _ _ hOk]
  exact lowEquivalent_smp_of_projection_and_confinement ctx observer hProj hConfined

-- ----------------------------------------------------------------------------
-- SM8.D.5 — at the one footprint SM3.C.9 has declared
-- ----------------------------------------------------------------------------
--
-- `lockSetForSyscall` is the SM3.C.9 seam: it resolves a syscall's declared
-- per-object footprint from the pre-state, and returns `none` where one has not
-- been established.  `.tcbSuspend` is the single declared arm today
-- (`lockSetForSyscall_undeclared_none` is the negative that keeps that honest),
-- so it is the one place the bracket §5 reasons about can be assembled from the
-- resolver rather than from an arbitrary `LockSet`.
--
-- The entry below is `Option`-valued **because the resolver is**: an undeclared
-- syscall has no footprint to bracket, and the caller must fall back to whatever
-- coarser serialisation it already has (today the SM5.I global kernel-entry
-- lock).  Returning a "best effort" set instead would be the one shape this must
-- not take — a declared lock set that does not cover a write is a *false*
-- footprint, and the 2PL argument would then rest on exclusion the runtime never
-- established.
--
-- ## Scope: this bracket is the OBJECT domain only
--
-- `LockSet` ranges over `LockId`, which is the SM0.I object domain — the
-- `objStore` table lock and the per-object locks.  A live `.tcbSuspend` also
-- takes locks in two domains this type cannot name:
--
-- * the **scheduler domain** — `suspendThreadOnCoreLockSet` over
--   `LockKey` (run queues of the core the victim is placed on and of the
--   executing core, plus replenish queues), and
-- * the **dynamic PIP chain** — SM3.C.11's contract requires each chain member's
--   TCB write lock *and* its home-core run-queue write lock, discovered as the
--   walk proceeds rather than resolvable from the pre-state at all.
--
-- So `syscallEntryUnderLockSet` is a witness that the *object*-domain bracket is
-- information-flow transparent, not a complete migration harness.  Composing the
-- three domains needs a `withLockSet` over `LockKey` (which strictly
-- contains `LockId` via its `.object` constructor) plus a fold that extends the
-- held set mid-transition — both SM3.C work, tracked there, and neither
-- affecting the §5 results, which never mention which objects a set names.
--
-- `declaredFootprintUncoveredDomains` below states that scope as data rather
-- than leaving it to this comment.

/-- SM8.D.5: the caller and decode a bracketed entry will actually run.

This replays exactly the prefix `syscallEntryChecked` runs before it dispatches —
reject the insecure default context, read the current thread **of the executing
core**, read that thread's registers, decode them against the layout — and
returns `none` wherever the entry itself would fail.  It exists so the declared
footprint can be resolved from the *same* decode the entry executes, rather than
from arguments a caller supplies alongside it. -/
def entryDecode (ctx : LabelingContext) (layout : SeLe4n.SyscallRegisterLayout)
    (executingCore : CoreId) (regCount : Nat) (s : SystemState) :
    Option (SeLe4n.ThreadId × SyscallDecodeResult) :=
  if isInsecureDefaultContext ctx then none
  else
    match s.scheduler.currentOnCore executingCore with
    | none => none
    | some tid =>
      match lookupThreadRegisterContext tid s with
      | .error _ => none
      | .ok (regs, _) =>
        match SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
                s tid layout regs regCount with
        | .error _ => none
        | .ok decoded => some (tid, decoded)

/-- SM8.D.5 (**the anti-drift tie**): where the replayed prefix gives up, the
real entry errors.

`entryDecode` duplicates `syscallEntryChecked`'s prefix, and a duplicated
computation is a drift risk unless something checks it against the original.
This is that check on the failing side: every `none` the helper returns is a
state on which the entry refuses, so a footprint is never resolved for an entry
that will not run. -/
theorem entryDecode_none_entry_error (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (h : entryDecode ctx layout executingCore regCount s = none) :
    ∃ e, syscallEntryChecked ctx layout executingCore regCount s = .error e := by
  unfold entryDecode at h
  unfold syscallEntryChecked
  cases hIns : isInsecureDefaultContext ctx with
  | true => exact ⟨.policyDenied, by simp⟩
  | false =>
    rw [hIns] at h
    simp only [Bool.false_eq_true, if_false] at h
    cases hCur : s.scheduler.currentOnCore executingCore with
    | none => exact ⟨.illegalState, by simp⟩
    | some tid =>
      rw [hCur] at h
      simp only at h
      cases hRegs : lookupThreadRegisterContext tid s with
      | error e => exact ⟨e, by simp [hRegs]⟩
      | ok regsPair =>
        obtain ⟨regs, stAfter⟩ := regsPair
        rw [hRegs] at h
        simp only at h
        cases hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
            s tid layout regs regCount with
        | error e => exact ⟨e, by simp [hRegs, hDec]⟩
        | ok decoded =>
          rw [hDec] at h
          exact absurd h (by simp)

/-- SM8.D.5 (**the anti-drift tie, success side**): where the replayed prefix
succeeds, the real entry dispatches on **exactly** those values.

`entryDecode_none_entry_error` covers only the failing side, which leaves a real
hole: if the two prefixes diverged while the helper still returned `some`, that
theorem stays true and silent, and `declaredLockSetForEntry` would go on
assembling a footprint from a caller and a decode the live entry does not use.
A new validation step added to `syscallEntryChecked`, or a normalisation applied
to its decode, would do exactly that.

This closes it in the strongest available form: the entry's whole behaviour is
pinned to the helper's outputs, not merely its prefix.  Whenever
`entryDecode` yields `(tid, decoded)`, the live entry **is**
`dispatchSyscallChecked` at that same `tid` and that same `decoded` — so a
divergence in either value stops this elaborating.

Preferred over factoring the shared prefix into one function: that would mean
reshaping a production entry point to suit a staged module, and it would pin
less, since a common prefix says nothing about what the entry does with its
result.

**WS-SM SM9.D.7 / PR #873 round 6.**  The equation used to spell the taint seam
out here, because the seam sat at the entry.  It sits at the dispatcher now, so
the entry *is* the dispatch at the filled state and the equation says exactly
that — the `tid`, the `decoded` and the state the dispatch runs on, all three
read off the helper's outputs.  Nothing was given up in the move: what the
propagation is keyed on is pinned one layer down and over *every* caller of the
dispatcher rather than over this entry alone, by
`dispatchSyscallChecked_applies_taint_plan`.  A decode normalisation or a new
validation step still stops this elaborating. -/
theorem entryDecode_some_entry_dispatches (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult)
    (h : entryDecode ctx layout executingCore regCount s = some (tid, decoded)) :
    syscallEntryChecked ctx layout executingCore regCount s
      = dispatchSyscallChecked ctx decoded tid executingCore
          (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore s executingCore tid
            decoded.overflowCount) := by
  unfold entryDecode at h
  unfold syscallEntryChecked
  cases hIns : isInsecureDefaultContext ctx with
  | true => rw [hIns] at h; exact absurd h (by simp)
  | false =>
    rw [hIns] at h
    simp only [Bool.false_eq_true, if_false] at h
    cases hCur : s.scheduler.currentOnCore executingCore with
    | none => rw [hCur] at h; exact absurd h (by simp)
    | some tid' =>
      rw [hCur] at h
      simp only at h
      cases hRegs : lookupThreadRegisterContext tid' s with
      | error e => rw [hRegs] at h; exact absurd h (by simp)
      | ok regsPair =>
        obtain ⟨regs, stAfter⟩ := regsPair
        rw [hRegs] at h
        simp only at h
        cases hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
            s tid' layout regs regCount with
        | error e => rw [hDec] at h; exact absurd h (by simp)
        | ok decoded' =>
          rw [hDec] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hTid, hDecoded⟩ := h
          subst hTid; subst hDecoded
          simp only [hRegs, hDec]
          rfl

/-- SM8.D.5: the target a capability-addressed syscall names, read the way the
live `dispatchWithCapChecked` arms read it.

Fail-closed three times over.

*The capability must name an object* — one that does not has no thread target.

*The target must pass `ThreadId.toValid?`* — the AL7-A sentinel guard the live
`.tcbSuspend` arm applies through `validateThreadIdArg` before it invokes the
handler.  Without it the resolver would declare a footprint for a syscall the
dispatch is going to reject, and under contention the bracket would enqueue
`lockCore` on locks for a call that cannot execute.

*The resolution must not leave the caller's root CNode.*  `resolveCapAddress`
walks a multi-level CSpace, reading each intermediate and leaf CNode on the
path; the footprint declares a read lock on the **root** only
(`lockSet_tcbSuspend`'s `cnodeRootObjId`), so a deeper path would have the
target selected by CNodes no declared lock covers — a concurrent writer could
redirect the resolution without conflicting with the footprint.  Locking the
whole path is not expressible: a `LockSet` is bounded by `maxLockSetSize`
while a CSpace path is bounded only by the address width, so the set cannot
name the path in general.  Rejecting is therefore the fail-closed option, and
it is the one the reviewer's own second alternative names.  A rejected entry
declares nothing and the caller keeps its coarser serialisation.

`resolveCapAddress` is run for the *guard* only; the capability itself still
comes from `syscallLookupCap`, so the target stays the one the live arm reads
rather than something this module computes for itself. -/
def entryCapTarget (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (s : SystemState) :
    Option SeLe4n.ThreadId :=
  match s.getTcb? tid with
  | none => none
  | some tcb =>
    match s.getCNode? tcb.cspaceRoot with
    | none => none
    | some rootCn =>
      -- Non-recursive **by construction**, not by inspecting the endpoint.
      -- `resolveCapAddress` consumes `guardWidth + radixWidth` bits per hop and
      -- recurses whenever any remain, so a root that consumes them all cannot
      -- descend at all.  Checking the final `ref.cnode` instead would accept a
      -- path that leaves the root and cycles back to it — the lookup would still
      -- have read an unlocked child CNode on the way, and a concurrent writer
      -- could redirect it without touching the declared footprint.
      if rootCn.depth ≠ rootCn.guardWidth + rootCn.radixWidth then none
      else
      match resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth s with
      | .error _ => none
      | .ok ref =>
        if ref.cnode ≠ tcb.cspaceRoot then none
        else
        match syscallLookupCap { callerId := tid, cspaceRoot := tcb.cspaceRoot,
                                 capAddr := decoded.capAddr, capDepth := rootCn.depth,
                                 requiredRight := syscallRequiredRight decoded.syscallId } s with
        | .error _ => none
        | .ok (cap, _) =>
          match cap.target with
          | .object objId =>
            match (SeLe4n.ThreadId.ofNat objId.toNat).toValid? with
            | none => none
            | some valid => some valid.val
          | _ => none

/-- SM8.D.5 (**the sentinel guard, as a theorem**): a capability naming the
sentinel thread yields no target, so no footprint is declared for it.

`ThreadId.sentinel` is the AL7-A rejected value; the live `.tcbSuspend` arm turns
it into `.invalidArgument` before the handler runs, so a footprint declared for it
would bracket a call that cannot execute. -/
theorem entryCapTarget_rejects_sentinel (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (s : SystemState) (t : SeLe4n.ThreadId)
    (h : entryCapTarget decoded tid s = some t) : t ≠ SeLe4n.ThreadId.sentinel := by
  unfold entryCapTarget at h
  split at h
  · exact absurd h (by simp)
  · next tcb _ =>
    split at h
    · exact absurd h (by simp)
    · next rootCn _ =>
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · next ref _ =>
          split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · next capPair _ =>
            obtain ⟨cap, _⟩ := capPair
            split at h
            · next objId _ =>
              split at h
              · exact absurd h (by simp)
              · next valid hValid =>
                have : t = valid.val := by simpa using h.symm
                rw [this]
                exact valid.property
            · exact absurd h (by simp)

/-- SM8.D.5 (**the resolution stays inside the locked CNode**): whenever a target
is resolved, the capability that named it lives in the caller's **root** CNode —
the one, and the only one, the declared footprint read-locks.

This is the property whose absence let a multi-level CSpace path select the target
through intermediate CNodes no declared lock covers.  It is stated over
`resolveCapAddress`'s own output rather than over the guard's syntax, so deleting
the `if` breaks this proof rather than silently widening the resolver again.

A `LockSet` cannot name a whole CSpace path — it is capped at `maxLockSetSize`,
a path is not — so single-level is the widest resolution this footprint can
honestly cover, and deeper ones are refused. -/
theorem entryCapTarget_single_level (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (s : SystemState) (t : SeLe4n.ThreadId)
    (h : entryCapTarget decoded tid s = some t) :
    ∃ tcb rootCn ref, s.getTcb? tid = some tcb ∧
      s.getCNode? tcb.cspaceRoot = some rootCn ∧
      -- The root consumes every bit, so the resolution takes exactly one hop:
      -- it cannot descend into a child CNode, and therefore cannot leave and
      -- re-enter the root either.
      rootCn.depth = rootCn.guardWidth + rootCn.radixWidth ∧
      resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth s = .ok ref ∧
      ref.cnode = tcb.cspaceRoot := by
  unfold entryCapTarget at h
  cases hTcb : s.getTcb? tid with
  | none => rw [hTcb] at h; exact absurd h (by simp)
  | some tcb =>
    rw [hTcb] at h
    simp only at h
    cases hCn : s.getCNode? tcb.cspaceRoot with
    | none => rw [hCn] at h; exact absurd h (by simp)
    | some rootCn =>
      rw [hCn] at h
      simp only at h
      by_cases hDepth : rootCn.depth = rootCn.guardWidth + rootCn.radixWidth
      · rw [if_neg (by exact fun hne => hne hDepth)] at h
        cases hRes : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth s with
        | error e => rw [hRes] at h; exact absurd h (by simp)
        | ok ref =>
          rw [hRes] at h
          simp only at h
          by_cases hSame : ref.cnode = tcb.cspaceRoot
          · exact ⟨tcb, rootCn, ref, by rfl, hCn, hDepth, hRes, hSame⟩
          · rw [if_pos hSame] at h
            exact absurd h (by simp)
      · rw [if_pos hDepth] at h
        exact absurd h (by simp)

/-- SM8.D.5: SM3.C.9's declared footprint **for the operation the entry will
actually execute**.

Every input `lockSetForSyscall` takes is derived here from the entry's own
resolution rather than supplied alongside it: the syscall id from the register
decode, the caller from the executing core's current thread, the target from the
capability that decode addresses.  An earlier cut took all three as free
parameters, which let a caller bracket `.tcbSuspend`'s footprint around whatever
the registers happened to decode to — a *false* footprint of exactly the kind the
section note above says must never be assembled, since the 2PL argument would
then rest on coverage nobody established. -/
def declaredLockSetForEntry (ctx : LabelingContext) (layout : SeLe4n.SyscallRegisterLayout)
    (executingCore : CoreId) (regCount : Nat) (s : SystemState) : Option LockSet :=
  match entryDecode ctx layout executingCore regCount s with
  | none => none
  | some (tid, decoded) =>
    match entryCapTarget decoded tid s with
    | none => none
    | some targetTid =>
      -- WS-RR RR7.10: the operands the entry resolved, in the shape the
      -- resolver now takes.  `entryCapTarget` yields a thread, so this is a
      -- thread-directed target.
      --
      -- WS-RR RR7.11 declared the seven IPC arms, and they read operands this
      -- shape leaves absent — an endpoint or notification `ObjId`, a `ReplyId`,
      -- and (for the two sending arms) the message, whose capabilities decide
      -- whether the receiver's CSpace root and the state-level lock are members.
      -- So this entry still declares exactly `.tcbSuspend`, and
      -- `lockSetForSyscall_ofThreadTarget_undeclared` is the theorem that says
      -- so from the operands rather than from the set of declared arms.
      --
      -- Supplying the rest belongs to **RR7.12**, at the production entry: the
      -- message is built by `resolveExtraCaps`, which mints CDT nodes, so the
      -- bracket has to decide which state it resolves the footprint at — and
      -- that decision is inseparable from the acquire/re-resolve/refuse
      -- discipline RR7.12 lands.  Doing it here would be that row's work in a
      -- module the kernel does not link.
      SeLe4n.Kernel.Concurrency.lockSetForSyscall decoded.syscallId
        (.ofThreadTarget tid targetTid) s

/-- SM8.D.5 (**the binding, as a theorem**): a resolved footprint is
`lockSetForSyscall`'s output at the **decoded** syscall id, the **executing
core's** caller, and the target that caller's capability names.

This is the property whose absence let the free-parameter form bracket an
unrelated operation.  It is stated rather than left to the reader of the
definition, so a future cut that reintroduces an independent argument has to
break a proof to do it. -/
theorem declaredLockSetForEntry_binds_decode (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (S : LockSet)
    (h : declaredLockSetForEntry ctx layout executingCore regCount s = some S) :
    ∃ tid decoded targetTid,
      entryDecode ctx layout executingCore regCount s = some (tid, decoded) ∧
      entryCapTarget decoded tid s = some targetTid ∧
      SeLe4n.Kernel.Concurrency.lockSetForSyscall decoded.syscallId
        (.ofThreadTarget tid targetTid) s = some S := by
  unfold declaredLockSetForEntry at h
  cases hDec : entryDecode ctx layout executingCore regCount s with
  | none => rw [hDec] at h; exact absurd h (by simp)
  | some pair =>
    obtain ⟨tid, decoded⟩ := pair
    rw [hDec] at h
    simp only at h
    cases hTgt : entryCapTarget decoded tid s with
    | none => rw [hTgt] at h; exact absurd h (by simp)
    | some targetTid =>
      rw [hTgt] at h
      simp only at h
      exact ⟨tid, decoded, targetTid, rfl, hTgt, h⟩

/-- SM8.D.5: the victim is an interior node of endpoint `ep`'s queue — the
situation in which suspending it splices it out and patches its neighbours.

**WS-OD (`v0.35.4`)**: the three *queued* blocking states, and not
`.blockedOnReply`.  A caller awaiting a reply has been dequeued — the rendezvous
that put it there took it off the endpoint's send queue — so the reply arm of
`cancelIpcBlocking` runs no `removeFromAllEndpointQueues`, splices nothing
(`cancelArmSpliceNeighbors?` is `(none, none)` there since WS-OD OD3.5) and
writes no endpoint of the victim's.  The fourth disjunct described a splice the
operation does not perform, and the footprint that used to carry an endpoint
member for it was over-declaring on the arm where that costs the most: the reply
arm is the widest one.  Derived from `cancelBlockedEndpoint?` rather than
re-matched, so the predicate and the footprint's own resolver cannot disagree
about which states are queued. -/
def victimBlockedOnEndpoint (victim : TCB) (ep : SeLe4n.ObjId) : Prop :=
  SeLe4n.Kernel.cancelBlockedEndpoint? victim = some ep

/-- SM8.D.5 (**the splice's neighbour writes are covered — the queue-owning-object
umbrella, as a theorem**).

Suspending a victim that sits *inside* an endpoint queue runs
`spliceOutMidQueueNode`, which patches the predecessor's `queueNext` and the
successor's `queuePrev` — writes to TCBs that are **not** the victim, and for
which the footprint carries no `tcbLock`.  Read on its own that is an uncovered
write, and it is what a comparison against `lockSet_cancelIpcBlockingOnCore`
(which does name both neighbours) suggests.

The reconciliation is the discipline `IPC/CrossCore/Cancellation.lean` states in
prose: an endpoint **owns** its queue, so the endpoint's write lock authorizes the
link writes of every TCB in that queue.  The sub-operation footprint names the
neighbours explicitly because it is the finer-grained authority; the syscall
footprint sits under the coarser umbrella.  Both are sound — but only one of them
was checked, and the write-membership family of the (then parametric) suspend
footprint stopped at six members, exactly where the umbrella began.  This is the
seventh.

**Why the conclusion has three parts, not one.**  A first cut concluded only
`(endpointLock ep, .write) ∈ S.pairs`, with the neighbour clause discharged by a
constant function that ignored its arguments.  That proved the endpoint lock is
*present*, which the family's endpoint member already said —
and it would have kept elaborating had the splice rewritten arbitrary unrelated
TCBs, so it established nothing about coverage.  The umbrella's actual content is
that each neighbour **is in the queue the endpoint owns**, so the second and third
clauses say so structurally: under `tcbQueueLinkIntegrity`, a spliced neighbour is
a real TCB whose own link points back at the victim (`queueNext = targetTid` for
the predecessor, `queuePrev = targetTid` for the successor).  An unrelated TCB
cannot satisfy that, which is exactly the discrimination the first cut lacked.

It is stated over the **resolved** footprint (`suspendFootprintOf`, what the SM8.D
resolver actually returns) rather than the parametric `lockSet_tcbSuspend`, and it
names the neighbours through the same `queueSpliceNeighbors?` the sub-operation
footprint reads, so it is a theorem about the splice rather than about the
endpoint lock in isolation.

**Why the footprint is not simply widened instead.**  Until WS-OD OD3.5 the
answer was arithmetic: the suspend footprint was eight members at full resolution
against a ceiling of nine, so two neighbour locks did not fit.  That reason is
spent — every raise since has left room, and at the time of writing
`lockSet_tcbSuspendOnCore_size_le_seventeen` sits well inside `maxLockSetSize`, so
the two would fit with room over.  (Both figures are derived and both have moved
repeatedly; the canonical live statement is the ceiling paragraph of
`LockSet.lean`, and this paragraph deliberately
quotes neither, because the decision below does not rest on them.)  The reason
that remains is the one that was always load-bearing: the members would be
**redundant**, not merely affordable.  The finer authority is already declared where it belongs, in the
sub-operation footprint (`lockSet_cancelIpcBlockingOnCore` names both
neighbours), and WS-RR RR7.38 turned the endpoint lock from an authorization
into an *exclusion* mechanism by making every footprint that can write a queued
TCB declare the queue owner's lock.  So adding them to the syscall footprint
would buy no new exclusion and would take that footprint to the ceiling, which
is contention — an observable channel here — for nothing.  The arithmetic is
recorded because a reader who checks it will find room; the decision does not
rest on there being none.

**What this theorem does *not* establish — and an earlier version of this
docstring wrongly claimed it did.**  This is an *authorization* statement: the
splice's neighbour writes fall under a lock the suspend holds.  Authorization is
not exclusion.  Exclusion additionally requires that **every** writer of a queued
TCB hold that endpoint's lock.

That was false until **WS-RR RR7.38**, which is why an earlier version of this
docstring wrongly read "there is no hole to close": there was one, in the
*inventory* rather than in this theorem, registered as
`UncoveredLockDomain.queueOwnershipProtocol` and exhibited as a `¬` by
`queueOwnership_violated_by_tcbSetPriority`.  It is closed: the eleven
footprints that can write a queued TCB now carry the queue owner's write lock as
a declared member, the `¬` is replaced by the eleven
`queueOwnership_respected_by_*` positives, and the domain constructor is gone. -/
theorem suspendFootprint_splice_neighbors_under_endpoint_lock (st : SystemState)
    (callerTid targetTid : SeLe4n.ThreadId) (S : LockSet) (victim : TCB)
    (ep : SeLe4n.ObjId)
    (hFp : SeLe4n.Kernel.Concurrency.suspendFootprintOf st callerTid targetTid = some S)
    (hVictim : st.getTcb? targetTid = some victim)
    (hBlocked : victimBlockedOnEndpoint victim ep)
    (hLinks : tcbQueueLinkIntegrity st) :
    (SeLe4n.Kernel.Concurrency.endpointLock ep, AccessMode.write) ∈ S.pairs ∧
      (∀ p, (SeLe4n.Model.queueSpliceNeighbors? victim).1 = some p →
        ∃ tcbP, st.getTcb? p = some tcbP ∧ tcbP.queueNext = some targetTid) ∧
      (∀ n, (SeLe4n.Model.queueSpliceNeighbors? victim).2 = some n →
        ∃ tcbN, st.getTcb? n = some tcbN ∧ tcbN.queuePrev = some targetTid) := by
  -- The SM6.E link invariant is phrased over the raw store, so the victim's
  -- membership is transported through the AL2-A accessor bridge rather than
  -- read raw here: the resolver itself reads through `getTcb?`, and a raw read
  -- in a theorem *about* it would be counted as an un-migrated access.
  have hVictimRaw := (SystemState.getTcb?_eq_some_iff st targetTid victim).mp hVictim
  refine ⟨?_, ?_, ?_⟩
  · -- **WS-OD (`v0.35.4`)**: one lift rather than a per-arm instantiation.  The
    -- suspend footprint is *defined over* the state-resolved cancellation
    -- footprint, which declares the blocked endpoint on the arm that splices, so
    -- the coverage crosses `_covers_cancelIpcBlockingOnCore` and the arm
    -- analysis happens once, where the resolver lives.
    obtain ⟨caller, hCaller, rfl⟩ :=
      SeLe4n.Kernel.Concurrency.suspendFootprintOf_eq_lockSet hFp
    exact SeLe4n.Kernel.lockSet_tcbSuspendOnCore_covers_cancelIpcBlockingOnCore
      st callerTid caller.cspaceRoot targetTid _
      (SeLe4n.Kernel.lockSet_cancelIpcBlockingOnCore_covers_blockedEndpoint
        st targetTid victim ep hVictim hBlocked)
  · -- The predecessor is a real TCB whose `queueNext` is the victim — so it is
    -- the victim's neighbour in the queue `ep` owns, not an arbitrary thread.
    intro p hp
    have hPrev : victim.queuePrev = some p := by
      simpa [SeLe4n.Model.queueSpliceNeighbors?] using hp
    obtain ⟨tcbP, hMemP, hNextP⟩ := hLinks.2 targetTid victim hVictimRaw p hPrev
    exact ⟨tcbP, (SystemState.getTcb?_eq_some_iff st p tcbP).mpr hMemP, hNextP⟩
  · -- …and symmetrically for the successor.
    intro n hn
    have hNext : victim.queueNext = some n := by
      simpa [SeLe4n.Model.queueSpliceNeighbors?] using hn
    obtain ⟨tcbN, hMemN, hPrevN⟩ := hLinks.1 targetTid victim hVictimRaw n hNext
    exact ⟨tcbN, (SystemState.getTcb?_eq_some_iff st n tcbN).mpr hMemN, hPrevN⟩

/-- SM8.D.5: the **queue-owning-object protocol**, as a predicate on a footprint.

A footprint that writes TCB `t` respects the protocol for endpoint `ep` when it
also holds `ep`'s write lock.  The discipline
`IPC/CrossCore/Cancellation.lean` states in prose is that this holds of *every*
footprint whose target is queued on `ep` — which is what would make the endpoint
lock an exclusion mechanism for queue-link writes rather than merely an
authorization for them. -/
def queueOwnershipRespectedBy (S : LockSet) (t : SeLe4n.ThreadId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) : Prop :=
  (SeLe4n.Kernel.Concurrency.tcbLock t, AccessMode.write) ∈ S.pairs →
    (o.lock, AccessMode.write) ∈ S.pairs

/-- SM8.D.5: the endpoint instance, which is the shape the splice argument uses.

**WS-RR RR7.38** generalised the predicate to any queue owner, because a thread
blocked on a *notification* sits in that object's queue on exactly the same
terms.  This abbreviation keeps the endpoint reading — the one the suspend
argument is stated in — spelled as it was. -/
def queueOwnershipRespected (S : LockSet) (t : SeLe4n.ThreadId)
    (ep : SeLe4n.ObjId) : Prop :=
  queueOwnershipRespectedBy S t (.endpoint ep)

/-- SM8.D.5: the suspend footprint **does** respect the protocol for its victim.

The positive half, and the reason the discipline looked complete: a suspend that
splices a victim out of `ep`'s queue holds `ep`'s write lock, so its own
queue-link writes are both authorized and mutually excluded against other
suspends on the same endpoint. -/
theorem suspendFootprint_respects_queueOwnership (st : SystemState)
    (callerTid targetTid : SeLe4n.ThreadId) (S : LockSet) (victim : TCB)
    (ep : SeLe4n.ObjId)
    (hFp : SeLe4n.Kernel.Concurrency.suspendFootprintOf st callerTid targetTid = some S)
    (hVictim : st.getTcb? targetTid = some victim)
    (hBlocked : victimBlockedOnEndpoint victim ep)
    (hLinks : tcbQueueLinkIntegrity st) :
    queueOwnershipRespected S targetTid ep :=
  fun _ => (suspendFootprint_splice_neighbors_under_endpoint_lock st callerTid targetTid
    S victim ep hFp hVictim hBlocked hLinks).1

/-! ## The capability-transfer destination — **covered at WS-RR RR7.8**

`capTransfer_receiverCnode_write_undeclared` stood here: concrete witnesses that
`lockSet_endpointSend` / `lockSet_endpointCall` declared no CNode **write**, so
the receiver's CSpace root — which `ipcUnwrapCaps` writes on a caps-carrying
rendezvous — had no covering lock.

It is deleted because the domain is covered, not to make a count fall.  RR7.7
gave both footprints a capability-transfer destination optional whose `some`
declares `(cnodeLock r, .write)` and `(stateLevelLock, .write)`; RR7.8 resolves
that optional from `rendezvousCapsDestination?`, the expression the WithCaps
arms themselves evaluate, and proves the closure:
`endpointSendDualWithCaps_object_writes_declared` and
`endpointCallWithCaps_object_writes_declared`
(`SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean`) say that **every object either
arm's transfer changes is declared write-mode in the footprint its bracket
acquires**.

A Tier-3 negative pins that the theorem and the constructor cannot return.
-/

/-- **WS-RR RR7.38**: a footprint whose last layer is the queue-owner member
holds that owner's write lock.

The one fact the eleven results below need, so it is proved once over the shape
rather than eleven times over the footprints. -/
theorem queueOwner_mem_write_of_extendOpt (S : LockSet)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    (o.lock, AccessMode.write) ∈
      (SeLe4n.Kernel.Concurrency.lockSetExtendOpt S
        (SeLe4n.Kernel.Concurrency.queueOwnerMember (some o))).pairs := by
  simp only [SeLe4n.Kernel.Concurrency.lockSetExtendOpt,
    SeLe4n.Kernel.Concurrency.queueOwnerMember, Option.map_some]
  exact SeLe4n.Kernel.self_write_mem_insertOrMerge _ o.lock

/-- **WS-RR RR7.38 (the domain, closed)**: every footprint that can write a
*queued* TCB respects the queue-ownership protocol.

This replaces `queueOwnership_violated_by_tcbSetPriority`, which stated the gap
as a `¬` precisely so that closing it would delete the theorem rather than leave
prose that had become false.  What closed it: each of these eleven footprints
now carries the queue owner's write lock as a declared member, resolved from the
pre-state by `queueOwnerAt`.  A suspend splicing a victim out of `ep`'s queue
holds `endpointLock ep .write`; any of these targeting one of that victim's
queued neighbours now holds the same lock, so the two are mutually excluded on
the TCBs the splice writes rather than merely authorized.

The cost is `permittedKinds` admitting `.endpoint` and `.notification` on those
eleven arms — two kinds, fixed by `QueueOwner.lock_kind`, rather than the
`.declassify` admit-everything shape — and it is the cheaper of the two options
the domain's own entry costed: the alternative was to let the suspend name both
neighbours' `tcbLock`s, which raises `maxLockSetSize` and so moves the WCRT
ceiling (`admissibleCriticalSection`) for every syscall. -/
theorem queueOwnership_respected_by_tcbSetPriority (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (neighbourTid : SeLe4n.ThreadId)
    (boundSchedContextId : Option SeLe4n.SchedContextId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_tcbSetPriority callerTid cnodeRootObjId
        neighbourTid boundSchedContextId (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o


/-- **WS-RR RR7.38**: the other ten arms that can write a queued TCB, each by the
same one-line argument.  They are eleven separate theorems because they are
eleven separate functions — the enumeration is of the *footprints*, not of a
property, and `permittedKinds`' own arms are what say which syscalls are in
scope. -/
theorem queueOwnership_respected_by_schedContextConfigure (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (scid : SeLe4n.SchedContextId)
    (neighbourTid : SeLe4n.ThreadId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_schedContextConfigure callerTid cnodeRootObjId scid (some neighbourTid) (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o

theorem queueOwnership_respected_by_schedContextBind (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (scid : SeLe4n.SchedContextId)
    (neighbourTid : SeLe4n.ThreadId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_schedContextBind callerTid cnodeRootObjId scid neighbourTid (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o

theorem queueOwnership_respected_by_schedContextUnbind (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (scid : SeLe4n.SchedContextId)
    (neighbourTid : SeLe4n.ThreadId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_schedContextUnbind callerTid cnodeRootObjId scid neighbourTid (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o

theorem queueOwnership_respected_by_tcbBindNotification (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId ntfnObjId : SeLe4n.ObjId) (neighbourTid : SeLe4n.ThreadId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_tcbBindNotification callerTid cnodeRootObjId ntfnObjId neighbourTid (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o

theorem queueOwnership_respected_by_tcbUnbindNotification (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId ntfnObjId : SeLe4n.ObjId) (neighbourTid : SeLe4n.ThreadId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_tcbUnbindNotification callerTid cnodeRootObjId ntfnObjId neighbourTid (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o

theorem queueOwnership_respected_by_tcbResume (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (neighbourTid : SeLe4n.ThreadId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_tcbResume callerTid cnodeRootObjId neighbourTid (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o

theorem queueOwnership_respected_by_tcbSetMCPriority (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (neighbourTid : SeLe4n.ThreadId)
    (boundSchedContextId : Option SeLe4n.SchedContextId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_tcbSetMCPriority callerTid cnodeRootObjId neighbourTid boundSchedContextId (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o

theorem queueOwnership_respected_by_tcbSetIPCBuffer (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (neighbourTid : SeLe4n.ThreadId)
    (targetVSpaceRootObjId : Option SeLe4n.ObjId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_tcbSetIPCBuffer callerTid cnodeRootObjId neighbourTid targetVSpaceRootObjId (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o

theorem queueOwnership_respected_by_tcbSetAffinity (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (neighbourTid : SeLe4n.ThreadId)
    (boundSchedContextId : Option SeLe4n.SchedContextId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_tcbSetAffinity callerTid cnodeRootObjId neighbourTid boundSchedContextId (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o

theorem queueOwnership_respected_by_tcbSetFaultHandler (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (neighbourTid : SeLe4n.ThreadId)
    (targetCnodeRootObjId handlerEndpointObjId : Option SeLe4n.ObjId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_tcbSetFaultHandler callerTid cnodeRootObjId neighbourTid targetCnodeRootObjId handlerEndpointObjId (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o

theorem queueOwnership_respected_by_tcbSetSpace (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (neighbourTid : SeLe4n.ThreadId)
    (newCnodeObjId newVSpaceRootObjId : Option SeLe4n.ObjId)
    (o : SeLe4n.Kernel.Concurrency.QueueOwner) :
    queueOwnershipRespectedBy
      (SeLe4n.Kernel.Concurrency.lockSet_tcbSetSpace callerTid cnodeRootObjId neighbourTid newCnodeObjId newVSpaceRootObjId (some o)) neighbourTid o :=
  fun _ => queueOwner_mem_write_of_extendOpt _ o

/-- SM8.D.5 (**fail-closed**): a footprint is declared only where the **decoded**
syscall is `.tcbSuspend`.

The undeclared property, restated over the operation the entry runs.  Under the
free-parameter form this could only be said about the caller's `sid` argument,
which is not what gets executed. -/
theorem declaredLockSetForEntry_undeclared (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult)
    (hDec : entryDecode ctx layout executingCore regCount s = some (tid, decoded))
    (hSid : decoded.syscallId ≠ .tcbSuspend) :
    declaredLockSetForEntry ctx layout executingCore regCount s = none := by
  unfold declaredLockSetForEntry
  rw [hDec]
  simp only
  cases hTgt : entryCapTarget decoded tid s with
  | none => rfl
  | some targetTid =>
    -- WS-RR RR7.11: through the thread-directed form.  The seven IPC arms are
    -- declared now, but they read operands `ofThreadTarget` leaves absent, so
    -- this entry resolver still declares exactly `.tcbSuspend` — and that is now
    -- a theorem about the operands rather than about the set of declared arms.
    exact SeLe4n.Kernel.Concurrency.lockSetForSyscall_ofThreadTarget_undeclared
      decoded.syscallId tid targetTid s hSid

/-- SM8.D.5: the lock domains a live `.tcbSuspend` needs that the object-domain
`LockSet` cannot express.

Data rather than prose, so the scope of `syscallEntryUnderDeclaredLockSet` is
checkable and a future cut that composes a domain has to delete an entry here
rather than quietly leave a stale comment. -/
inductive UncoveredLockDomain where
  -- **WS-RR RR8.12 Cut C6h (`v0.35.181`)**: `syscallSeamSchedulerDomain` is
  -- DELETED.  The syscall seam brackets on the scheduler domain now:
  -- `syscallDispatchCrossCoreBracketedStep` runs the seam's `BracketSpec`
  -- (`syscallDispatchBracket`, WS-LS LS2.4) over `declaredUnifiedLockSetForAbiEntry`, whose
  -- `LockKey` members name the run-queue and replenish-queue locks the
  -- constructor said a `LockSet` could not express, and each of the sixteen
  -- declared arms carries a `schedLockSet_*_coversWrites` proof that reaches the
  -- acquired set through `unifiedLockSetForSyscall_coversWrites`.
  --
  -- The constructor's stated reason for the syscall half being its own cut is
  -- **corrected** rather than merely satisfied: it read *"the object-domain
  -- syscall footprints hold `stateLevelLock` and per-object locks, **not** the
  -- object-store table lock"*, and `stateLevelLock` IS the object-store table
  -- lock — a `.objStore`-kinded `LockId` names no object, so every one of
  -- them is the one table key.  The two domains were therefore never
  -- two locks, which is why the cut unifies the footprints rather than
  -- nesting two brackets: nesting would take that one word twice and walk the
  -- SM0.I ladder backwards.
  /-- WS-SM SM9.D.17 (audit): the **taint table's per-key realisation**.

  Every content-moving syscall writes `SystemState.declassificationTaint` at the
  keys its plan names, and declares the *objects'* own locks for them — a
  deliberate choice, since `stateLevelLock` on the eight content-moving arms
  would serialise unrelated IPC on unrelated endpoints and break the tick-budget
  fit the IPC suites pin.  The **model**, though, replaces the field whole:
  `TaintTable.set` returns a table built from the pre-state's entries.  So the
  key-local reading is sound only once the runtime realises the table as
  per-object storage; until it does, two cores committing disjoint taint keys
  from their own pre-states would each write the whole field and the later commit
  would discard the other's provenance.

  Not a live race — SM5.I's global entry lock serialises every commit, and
  `withLockSet` is deferred at the export bodies (SM3.C.9).  `SystemState.objects`
  carries the identical obligation for `storeObject` under the same discipline,
  which is why the owner is the representation cut rather than this phase.
  Registered here rather than left in `TaintPropagation`'s prose because that is
  the difference between an obligation a later cut must discharge and one it can
  forget: the completeness theorem below now fails until this entry is removed. -/
  | taintTablePerKeyStore
  deriving DecidableEq, Repr

/-- SM8.D.5: the domains this bracket does **not** cover, and the workstream that
owns composing them.

**Owners re-pointed at v0.34.26 (WS-RR RR0.9).**  Five of the six named a
sub-task inside SM3, a phase closed at v0.31.9 — `SM3.B` three times, plus
`SM3.C.9` and `SM3.C.11`.  (The debt sweep reported three; it counted the
literal `SM3.B` trio.)  An owner field naming a closed phase does not identify anyone who
can close the domain, which is the same defect as a closure target inside a
plan marked LANDED, and it is the reason the debt sweep found this register
incoherent.  Each now names a **live** target; the fine-lock tracks are
enumerated in `docs/planning/SMP_FINE_LOCK_MIGRATION_PLAN.md` and the register
row for each sits in `docs/REGISTERED_DEBT.md`.

**Three owners re-pointed again at v0.34.47 (PR #888 review).**  Track C's own
rows (RR7.10–RR7.13) generalise the resolver, declare the IPC footprints and
bracket the dispatch body; none of them acquires a per-core scheduler lock,
extends a lock set along a PIP chain, or couples locks down a CSpace walk, so
naming that range left three domains with an owner that could not close them.
Each now names the closure row written for it: RR7.39 (the scheduler domain —
the fine-lock plan's SM3.C.9.b follow-on), RR7.40 (the dynamic PIP chain),
RR7.41 (the CSpace-walk interior).

**The CSpace-walk interior's entry is deleted at v0.34.90 (WS-RR RR7.41).**
`Capability.cspaceWalkPath` derives the CNodes a resolution passes through from
`resolveCapAddress`'s own recursion, `cspaceWalkLockSet` declares a **read** lock
on each, and `cspaceWalk_conflicts_with_delete` proves what the root-only
footprint could not: a `cspaceDelete` whose target lies on the path shares a
conflicting lock with the resolution, so SM3.E's conflict order separates them.
The footprint is declared as a sorted set (`cspaceWalkBracket`, a `BracketSpec`
since WS-LS LS2.4) rather than acquired by a hand-over-hand coupling walk —
coupling would abandon the SM0.I total order the whole tree's deadlock freedom
rests on, and the declared footprint buys the same exclusion while keeping it.  Two relations PR #892 review round 4 closed
in that mechanism: the declaration is **refused** above `maxLockSetSize`
(`declaredLockSetForCSpaceWalk` answers `none` for a walk past the ceiling and
the bracket falls back — a footprint the bound is false for is never claimed),
and a **failed** lookup is a read the footprint names: a key holding no CNode
declares `stateLevelLock` in read mode (`cspaceWalkKeyLock`), which conflicts
with the write every structural writer declares.

**The dynamic PIP chain's entry is deleted at v0.34.90 (WS-RR RR7.40).**  Its
locks are nameable now that RR7.39 gave the scheduler domain a runtime:
`PriorityInheritance.pipChainSchedFootprint` declares every visited thread's TCB
write lock **and** its home core's run-queue write lock — two segments, because
the `LockKey` ladder puts every object lock below every run-queue lock and
per-member coupling would walk it backwards.  The footprint is declared
statically at the seams that walk the chain (the receive and reply footprints
simulate the walk, `pipChainVisited`), and
`propagatePipChainCrossCore_coversWrites` proves the walk writes nothing outside
it; the runtime extension that acquired it (`withPipChainSchedExtension`, PR
#892 review round 2) is deleted with the word-level bracket at WS-LS LS2.4.  The entry goes rather than narrows because the walk is now covered end to
end; the inventory falls from four to three, which is the only reason it may.

**The scheduler domain's entry is DELETED at v0.35.181 (WS-RR RR8.12 Cut C6h).**
RR7.39 (v0.34.89) closed the *entries*' half — the three per-core scheduler seams
acquire their declared footprints over a domain it built — and narrowed the
constructor to `syscallSeamSchedulerDomain`, the syscall half.  RR8.12 closed
that half in sequence: the shared core segment, then sixteen per-arm footprints,
then a coverage proof for each, then the seam's bracket.  The entry goes rather
than narrows because the syscall seam is now bracketed on the scheduler domain
end to end; **the inventory falls from two to one**, which is the only reason it
may.

One correction the deletion carries, because the retired constructor's own stated
reason was false: it said the object-domain syscall footprints hold
`stateLevelLock` *"**not** the object-store table lock"*.  They are the same lock
— a `.objStore`-kinded `LockId` names no object, so every one of them is the one
table key — and the two domains were never two locks, and
the seam acquires **one** unified footprint (`declaredUnifiedLockSetForAbiEntry`)
rather than nesting two brackets that would take that word twice. -/
def declaredFootprintUncoveredDomains : List (UncoveredLockDomain × String) :=
  [(.taintTablePerKeyStore, "SM10.1 (fine-lock Track D)"),
]

/-- SM8.D.5: the exhaustive list of uncovered domains, in the shape the claim
inventory uses — so completeness can be quantified over the *constructors*
rather than compared against a literal. -/
def UncoveredLockDomain.all : List UncoveredLockDomain :=
  [.taintTablePerKeyStore]

/-- SM8.D.5: every constructor is listed.  This is the clause a literal
comparison cannot supply: adding a new domain makes `cases d` non-exhaustive
here, so the registration has to be amended in the same cut. -/
theorem UncoveredLockDomain.mem_all (d : UncoveredLockDomain) : d ∈ UncoveredLockDomain.all := by
  cases d <;> decide

theorem UncoveredLockDomain.all_nodup : UncoveredLockDomain.all.Nodup := by decide

/-- SM8.D.5: every uncovered domain is registered, each against an owner — the
completeness check on the list above.

**Quantified over the type, not against a literal.**  An earlier cut compared
`declaredFootprintUncoveredDomains.map Prod.fst` to a two-element literal, which
a third constructor would leave elaborating unchanged: the debt inventory could
then omit a newly discovered domain while every migration check kept passing,
and the object-only bracket would be treated as covering more of the syscall
than it does.  The first conjunct now says every *constructor* is registered, via
`UncoveredLockDomain.mem_all`, whose proof is a `cases` that stops being
exhaustive the moment a domain is added. -/
theorem declaredFootprintUncoveredDomains_complete :
    (∀ d : UncoveredLockDomain, d ∈ declaredFootprintUncoveredDomains.map Prod.fst) ∧
      (declaredFootprintUncoveredDomains.map Prod.fst).Nodup ∧
      declaredFootprintUncoveredDomains.all (fun d => !d.2.isEmpty) := by
  refine ⟨fun d => ?_, ?_, ?_⟩
  · cases d <;> decide
  · decide
  · rfl

/-- **WS-SM SM8.D.5 (PR #873 round 6): may the declared footprints be relied on
as a complete serialization discipline yet?**

`false`, and the point is that it is now a *decidable predicate a consumer can
consult* rather than a sequencing intention recorded in prose.

Every entry in `declaredFootprintUncoveredDomains` names a write the bracket does
not order.  `taintTablePerKeyStore` is the sharpest of them: the model replaces
`SystemState.declassificationTaint` whole, so two cores committing **disjoint**
taint keys from their own pre-states would each write the whole field and the
later commit would discard the other's provenance — a lost causal chain, which is
the direction this subsystem must never err in.  The same is true of
`SystemState.objects` under `storeObject`, which is why the per-key realisation
is a property of the *commit*, not of this field: a per-key taint store shipped
on its own would leave the identical lost update reachable through the object
store, so the two land together in the commit-partitioning cut (SM10.1 / the
`SMP_FINE_LOCK_MIGRATION_PLAN` Track D) or neither does.

**What this buys.**  The reviewer's ask on PR #873 was "implement that
representation *before* relying on key-local locking".  Before was already the
plan; it was not enforced.  It is now: reliance is gated on this flag,
`fineLockDiscipline_requires_every_domain_covered` says the flag can only become
`true` by emptying the inventory, and `fineLockDisciplineComplete_is_false` pins
that it has not.  A cut that enables SM3.C.9's fine locks while a domain is still
registered has to delete an entry it cannot honestly delete. -/
def fineLockDisciplineComplete : Bool :=
  declaredFootprintUncoveredDomains.isEmpty

/-- SM8.D.5 (PR #873 round 6): **it is false today**, and this is the pin that
makes flipping it a deliberate act.  Deleting it is the same edit as claiming
every registered domain is covered.

**How many that is, is deliberately not written here.**  It was — "six of them
today", which had already drifted to seven by the time WS-RR RR7.8 deleted
`capTransferReceiverCnode` and made it six again by coincidence.  A number
restated beside the list it counts is the shape the sentence itself warns
against; the count is `declaredFootprintUncoveredDomains.length` and nothing
else. -/
theorem fineLockDisciplineComplete_is_false : fineLockDisciplineComplete = false := by
  decide

/-- SM8.D.5 (PR #873 round 6): **the interlock.**  The discipline is complete
exactly when no domain is registered as uncovered — so a per-key taint store, a
covering CNode write member and the scheduler-domain bracket are each a
*precondition* of relying on declared footprints, not work that may run
alongside it. -/
theorem fineLockDiscipline_requires_every_domain_covered :
    fineLockDisciplineComplete = true ↔ declaredFootprintUncoveredDomains = [] := by
  unfold fineLockDisciplineComplete
  exact List.isEmpty_iff

/-- SM8.D.5 (PR #873 round 6): **and the taint store specifically gates it.**

Named on its own because it is the entry PR #873's review pressed twice, and
because a reader should be able to check the dependency without reconstructing it
from the list: while `taintTablePerKeyStore` is registered, the flag is false, so
nothing may treat a key-local taint write as serialised by the key's own lock. -/
theorem taintPerKeyStore_blocks_fineLockDiscipline
    (h : UncoveredLockDomain.taintTablePerKeyStore
      ∈ declaredFootprintUncoveredDomains.map Prod.fst) :
    fineLockDisciplineComplete = false := by
  cases hEmpty : declaredFootprintUncoveredDomains with
  | nil => rw [hEmpty] at h; simp at h
  | cons a rest => simp [fineLockDisciplineComplete, hEmpty]

/-- SM8.D.5 (**WS-LS LS2.1**: over the pair): the 2PL-bracketed live entry
**over the declared footprint** — `declaredLockSetForEntry`'s output at the
kernel half, bracketed, or `none` where no footprint is declared for the
operation the entry will run. -/
def syscallEntryUnderDeclaredLockSet (ctx : LabelingContext) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SeLe4n.Kernel.Concurrency.LockedSystemState) :
    Option (SeLe4n.Kernel.Concurrency.LockedSystemState × Except KernelError Unit) :=
  (declaredLockSetForEntry ctx layout executingCore regCount s.kernel).map
    (fun S => syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s)

/-- SM8.D.5 (**why the shrinking phase needs a withdrawal**): a release by a
core that is not a holder is the identity, so it cannot remove that core's
*queued* request.

Both release arms of `applyOp` guard on holdership — `releaseRead` on membership
in `readers`, `releaseWrite` on `writerHeld = some core` — and return the state
unchanged otherwise.  A queued acquisition is therefore untouched by a
release-only shrinking phase, which is what made the refusal path's unwind
partial under contention.

The theorem is unchanged; what changed is what it implies about this tree.
`RwLockOp.cancel` exists (WS-LC LC1), the shrinking phase is `unwindAll` and
withdraws before it releases (LC4.1), and
`LockState.unwindAll_not_queued` closes the gap this result identifies.
It is kept, and kept in this form, because it is the *reason* the withdrawal
has to exist: delete the withdrawal and this theorem is exactly the defect
that comes back. -/
theorem rwLock_release_by_nonholder_preserves_waiters (l : RwLockState) (c : CoreId)
    (hNotReader : c ∉ l.readers) (hNotWriter : l.writerHeld ≠ some c) :
    (l.applyOp (.releaseRead c)).waiters = l.waiters ∧
      (l.applyOp (.releaseWrite c)).waiters = l.waiters := by
  constructor
  · show (if c ∉ l.readers then l else _).waiters = l.waiters
    rw [if_pos hNotReader]
  · show (if l.writerHeld ≠ some c then l else _).waiters = l.waiters
    rw [if_pos hNotWriter]

/-- SM8.D.5 (**fail-closed**): every syscall other than `.tcbSuspend` is
undeclared, so no footprint is bracketed and the caller keeps its existing
serialisation.  This is `declaredLockSetForEntry_undeclared` lifted to the
bracketed entry — the property that stops a future cut from silently bracketing
an operation whose coverage proof does not exist yet. -/
theorem syscallEntryUnderDeclaredLockSet_undeclared (ctx : LabelingContext) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult)
    (hDec : entryDecode ctx layout executingCore regCount s.kernel = some (tid, decoded))
    (hSid : decoded.syscallId ≠ .tcbSuspend) :
    syscallEntryUnderDeclaredLockSet ctx lockCore layout executingCore regCount s = none := by
  unfold syscallEntryUnderDeclaredLockSet
  rw [declaredLockSetForEntry_undeclared ctx layout executingCore regCount s.kernel tid decoded
    hDec hSid]
  rfl

/-- SM8.D.5: and nothing is bracketed where the entry itself would refuse —
the bracket never runs ahead of a decode that does not exist. -/
theorem syscallEntryUnderDeclaredLockSet_no_decode (ctx : LabelingContext) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SeLe4n.Kernel.Concurrency.LockedSystemState)
    (h : entryDecode ctx layout executingCore regCount s.kernel = none) :
    syscallEntryUnderDeclaredLockSet ctx lockCore layout executingCore regCount s = none := by
  unfold syscallEntryUnderDeclaredLockSet declaredLockSetForEntry
  rw [h]
  rfl

/-- SM8.D.5 (**the headline at the declared footprint**): when SM3.C.9's
resolver yields a footprint for `.tcbSuspend`, the entry bracketed in **that**
footprint is non-interfering on every core.

The resolution hypothesis is *consumed*, not decorative: it is what turns the
`Option` the resolver returns into the `some` the conclusion names.  An earlier
cut stated this over an arbitrary `LockSet` with the resolver equation hanging
off it unused, which asserted nothing about the footprint the migration will
actually install. -/
theorem suspendUnderDeclaredLockSet_preserves_projectionOnCore_atCore (ctx : LabelingContext)
    (observer : IfObserver) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId)
    (regCount : Nat) (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (st' : SystemState)
    (c' : CoreId)
    (hFootprint : declaredLockSetForEntry ctx layout executingCore regCount s.kernel = some S)
    (hOk : syscallEntryChecked ctx layout executingCore regCount s.kernel = .ok ((), st'))
    (hProjOn : projectStateOnCore ctx observer st' c'
        = projectStateOnCore ctx observer s.kernel c')
    (hConfined : observableSlotsConfinedToCore s.kernel st' c') :
    ∃ r, syscallEntryUnderDeclaredLockSet ctx lockCore layout executingCore regCount s = some r ∧
      lowEquivalent_smp ctx observer r.1.kernel s.kernel := by
  refine ⟨syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s, ?_, ?_⟩
  · unfold syscallEntryUnderDeclaredLockSet
    rw [hFootprint]
    rfl
  · exact syscallEntryUnderLockSet_preserves_projectionOnCore_atCore ctx observer S lockCore
      layout executingCore regCount s st' c' hOk hProjOn hConfined

/-- SM8.D.5: the boot-core instance of the declared-footprint headline.

`.tcbSuspend` executing on a secondary core writes that core's scheduler slots,
so boot-core confinement is false for it and this form says nothing about the
case the migration cares about — `…_atCore` is the one to reach for.  Kept
because a caller holding the boot-pinned whole-projection fact can discharge its
premise directly. -/
theorem suspendUnderDeclaredLockSet_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId)
    (regCount : Nat) (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (st' : SystemState)
    (hFootprint : declaredLockSetForEntry ctx layout executingCore regCount s.kernel = some S)
    (hOk : syscallEntryChecked ctx layout executingCore regCount s.kernel = .ok ((), st'))
    (hProj : projectState ctx observer st' = projectState ctx observer s.kernel)
    (hConfined : observableSlotsConfinedToCore s.kernel st' bootCoreId) :
    ∃ r, syscallEntryUnderDeclaredLockSet ctx lockCore layout executingCore regCount s = some r ∧
      lowEquivalent_smp ctx observer r.1.kernel s.kernel := by
  refine suspendUnderDeclaredLockSet_preserves_projectionOnCore_atCore ctx observer S lockCore
    layout executingCore regCount s st' bootCoreId hFootprint hOk ?_ hConfined
  rw [projectStateOnCore_bootCore, projectStateOnCore_bootCore]
  exact hProj

/-- SM8.D.5: the fail-closed half at the declared footprint — a refused suspend
moves the ghost lock table and nothing else (the kernel half is identical),
and is invisible on every core.

**WS-LS LS2.1 (strengthened).**  Over the pair; the middle conjunct is
sharpened from `lockWritesOnly s r.1` to `r.1.kernel = s.kernel`, and
`hInv : s.objects.invExt` is dropped. -/
theorem suspendUnderDeclaredLockSet_failClosed_invisible (ctx : LabelingContext) (S : LockSet)
    (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (e : KernelError) (L : SecurityLabel)
    (hFootprint : declaredLockSetForEntry ctx layout executingCore regCount s.kernel = some S)
    (hDenied : syscallEntryChecked ctx layout executingCore regCount s.kernel = .error e) :
    ∃ r, syscallEntryUnderDeclaredLockSet ctx lockCore layout executingCore regCount s = some r ∧
      r.1.kernel = s.kernel ∧
      ∀ c : CoreId,
        ObservableState.onCore ctx c L r.1.kernel = ObservableState.onCore ctx c L s.kernel := by
  refine ⟨syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s, ?_, ?_, ?_⟩
  · unfold syscallEntryUnderDeclaredLockSet
    rw [hFootprint]
    rfl
  · exact (syscallEntryUnderLockSet_failClosed ctx S lockCore layout executingCore regCount s e
      hDenied).1
  · exact syscallEntryUnderLockSet_failClosed_invisible ctx S lockCore layout executingCore
      regCount s e L hDenied

/-- SM8.D.5 (**the resolved footprint is the suspend footprint**): a declared
footprint resolves only through `suspendFootprintOf`, at the caller and target the
entry's own decode names.

`declaredLockSetForEntry_binds_decode` says the inputs come from the decode;
this says what the output then is, so the two together pin the whole resolution
rather than only its shape. -/
theorem declaredLockSetForEntry_is_suspend_footprint (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (S : LockSet)
    (h : declaredLockSetForEntry ctx layout executingCore regCount s = some S) :
    ∃ tid decoded targetTid,
      entryDecode ctx layout executingCore regCount s = some (tid, decoded) ∧
      decoded.syscallId = .tcbSuspend ∧
      entryCapTarget decoded tid s = some targetTid ∧
      SeLe4n.Kernel.Concurrency.suspendFootprintOf s tid targetTid = some S := by
  obtain ⟨tid, decoded, targetTid, hDec, hTgt, hLock⟩ :=
    declaredLockSetForEntry_binds_decode ctx layout executingCore regCount s S h
  by_cases hSid : decoded.syscallId = .tcbSuspend
  · refine ⟨tid, decoded, targetTid, hDec, hSid, hTgt, ?_⟩
    rw [hSid, SeLe4n.Kernel.Concurrency.lockSetForSyscall_tcbSuspend] at hLock
    exact hLock
  · exact absurd hLock (by
      rw [SeLe4n.Kernel.Concurrency.lockSetForSyscall_ofThreadTarget_undeclared
        decoded.syscallId tid targetTid s hSid]
      simp)

-- ============================================================================
-- §6  SM8.D — the phase's claims as data, each carrying its own proof
-- ============================================================================
--
-- The same device SM8.B gave the covert-channel inventory and SM8.C gave the
-- cross-core declassification rules: the sub-tasks are a finite enum, the claim
-- each one makes is a `Prop` computed from the id, and the evidence is a
-- dependently-typed function that must *inhabit* that `Prop`.  A claim whose
-- theorem is renamed fails to elaborate; a claim mapped to the wrong theorem
-- fails to typecheck; a sub-task added without evidence leaves the match
-- non-exhaustive.

/-- SM8.D: the phase's claims.  Six ids for five sub-tasks — D.3 and D.5 each
make two: D.3 refutes the model-level reading *and* bounds the timing one that
replaces it, and D.5 covers the successful path *and* the refused one.  SM8.D.6
is the scenario suite and carries no Lean claim. -/
inductive FineLockClaimId where
  /-- SM8.D.1 — an observer sees nothing of a lock word. -/
  | lockStateInvisible
  /-- SM8.D.2 — reader multiplicity is not directly observable. -/
  | readerMultiplicityHidden
  /-- SM8.D.3 — writer exclusion is not observable to a blocked acquirer either. -/
  | writerExclusionHidden
  /-- SM8.D.3 — what the blocked acquirer *does* observe is bounded. -/
  | contentionDelayBounded
  /-- SM8.D.4 — the 2PL bracket makes no write standard BIBA forbids. -/
  | integrityUnderLocks
  /-- SM8.D.4 — nor any write seLe4n's *authority* order forbids.

  A separate id rather than a second reading of the one above, because
  `writeRules_differ` says these are two claims: a deployment configured with one
  order gets nothing from a result about the other.  With a single arm the
  dependent inventory would keep elaborating if the authority-order theorem were
  weakened or stopped proving the advertised property. -/
  | authorityIntegrityUnderLocks
  /-- SM8.D.5 — a bracketed live entry is non-interfering when its dispatch is. -/
  | secureFlowUnderFineLocks
  /-- SM8.D.5 — and a refused one is invisible outright. -/
  | failClosedUnderFineLocks
  /-- SM8.D.3 — CC-5's inventory entry is backed by the bound, not by prose. -/
  | contentionChannelRegistered
  deriving DecidableEq, Repr

def FineLockClaimId.all : List FineLockClaimId :=
  [ .lockStateInvisible, .readerMultiplicityHidden, .writerExclusionHidden
  , .contentionDelayBounded, .integrityUnderLocks, .authorityIntegrityUnderLocks
  , .secureFlowUnderFineLocks, .failClosedUnderFineLocks
  , .contentionChannelRegistered ]

theorem FineLockClaimId.mem_all (id : FineLockClaimId) : id ∈ FineLockClaimId.all := by
  cases id <;> decide

theorem FineLockClaimId.all_nodup : FineLockClaimId.all.Nodup := by decide

theorem fineLockClaims_count : FineLockClaimId.all.length = 9 := by rfl

/-- SM8.D: the plan sub-task each claim discharges. -/
def FineLockClaimId.subTask : FineLockClaimId → String
  | .lockStateInvisible => "SM8.D.1"
  | .readerMultiplicityHidden => "SM8.D.2"
  | .writerExclusionHidden => "SM8.D.3"
  | .contentionDelayBounded => "SM8.D.3"
  | .integrityUnderLocks => "SM8.D.4"
  | .authorityIntegrityUnderLocks => "SM8.D.4"
  | .secureFlowUnderFineLocks => "SM8.D.5"
  | .failClosedUnderFineLocks => "SM8.D.5"
  | .contentionChannelRegistered => "SM8.D.3"

/-- SM8.D: **every proof-carrying sub-task of the phase is claimed.**  D.6 is
the scenario suite (`tests/SmpInformationFlowSuite.lean` §7), which is a Tier-2
runner rather than a theorem, so it is deliberately absent. -/
theorem fineLockClaims_cover_subTasks :
    FineLockClaimId.all.map FineLockClaimId.subTask
      = ["SM8.D.1", "SM8.D.2", "SM8.D.3", "SM8.D.3", "SM8.D.4", "SM8.D.4", "SM8.D.5",
         "SM8.D.5", "SM8.D.3"] := by
  rfl

/-- SM8.D: the name of the theorem that discharges each claim, compile-time
validated through `niName!` so a rename is a build failure. -/
def fineLockClaimTheorem : FineLockClaimId → String
  | .lockStateInvisible => niName! onCore_lock_indistinguishable
  | .readerMultiplicityHidden => niName! readerMultiplicity_not_observable
  | .writerExclusionHidden => niName! blockedAcquirer_observes_nothing
  | .contentionDelayBounded => niName! lockContention_delay_bounded
  | .integrityUnderLocks => niName! bibaIntegrity_underLockSet
  | .authorityIntegrityUnderLocks => niName! authorityIntegrity_underLockSet
  | .secureFlowUnderFineLocks => niName! syscallEntryUnderLockSet_preserves_projectionOnCore_atCore
  | .failClosedUnderFineLocks => niName! syscallEntryUnderLockSet_failClosed_invisible
  | .contentionChannelRegistered => niName! acceptedCovertChannel_lockContention_bounded

theorem fineLockClaimTheorem_nodup :
    (FineLockClaimId.all.map fineLockClaimTheorem).Nodup := by decide

/-- SM8.D: **the property each claim must establish.**

Stated as a computed `Prop` rather than as a string, for the reason SM8.B's
`CovertChannelId.evidenceProp` gives: a name-validated table checks only that
the name resolves, so mapping a claim at the *wrong* theorem passes it.  Here
each arm is the conclusion of the theorem `fineLockClaimTheorem` names, so
supplying a different one is a type error. -/
def FineLockClaimId.evidenceProp : FineLockClaimId → Prop
  | .lockStateInvisible =>
      ∀ (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s : LockedSystemState)
        (k : LockKey) (l₁ l₂ : RwLockState),
        ObservableState.onCore ctx c L (setLockAt s k l₁).kernel
          = ObservableState.onCore ctx c L (setLockAt s k l₂).kernel
  | .readerMultiplicityHidden =>
      ∀ (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s : LockedSystemState)
        (k : LockKey) (readers₁ readers₂ : List CoreId),
        ObservableState.onCore ctx c L
            (setLockAt s k { RwLockState.unheld with readers := readers₁ }).kernel
          = ObservableState.onCore ctx c L
            (setLockAt s k { RwLockState.unheld with readers := readers₂ }).kernel
  | .writerExclusionHidden =>
      ∀ (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s : LockedSystemState)
        (k : LockKey) (holder : CoreId) (mode : AccessMode),
        ObservableState.onCore ctx c L
            (setLockAt s k
              { RwLockState.unheld with writerHeld := some holder, waiters := [(c, mode)] }).kernel
          = ObservableState.onCore ctx c L (setLockAt s k RwLockState.unheld).kernel
  | .contentionDelayBounded =>
      ∀ (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (maxDelay : Nat),
        SeLe4n.Kernel.Concurrency.FairTrace e maxDelay →
        e.initial = RwLockState.unheld →
        ∀ (c : CoreId) (m : AccessMode) (kEnq : Nat),
          (c, m) ∈ (e.stateAt kEnq).waiters →
          kEnq + lockContentionDelayBound maxDelay < e.ops.length →
          -- The waiter does not withdraw inside the window the bound covers:
          -- a cancelled request is never admitted, so there is no observation
          -- to bound.  Carried in the evidence obligation rather than left to
          -- the theorem alone, so a future weakening of the premise is a type
          -- error here too.
          e.noCancelIn c kEnq (kEnq + lockContentionDelayBound maxDelay + 1) →
          ∃ delay, lockContentionObservation e c kEnq = some delay ∧
            delay ≤ lockContentionDelayBound maxDelay
  | .integrityUnderLocks =>
      ∀ (α : Type) (ctx : LabelingContext) (subject : SecurityLabel) (S : LockSet) (core : CoreId)
        (action : SystemState → SystemState × α) (s : LockedSystemState),
        noUnpermittedWrite (bibaWritePermitted ctx subject) s.kernel (action s.kernel).1 →
        noUnpermittedWrite (bibaWritePermitted ctx subject) s.kernel
          (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1.kernel
  | .authorityIntegrityUnderLocks =>
      ∀ (α : Type) (ctx : LabelingContext) (subject : SecurityLabel) (S : LockSet) (core : CoreId)
        (action : SystemState → SystemState × α) (s : LockedSystemState),
        noUnpermittedWrite (authorityWritePermitted ctx subject) s.kernel (action s.kernel).1 →
        noUnpermittedWrite (authorityWritePermitted ctx subject) s.kernel
          (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1.kernel
  | .secureFlowUnderFineLocks =>
      -- Quantified over the confinement core `c'`, NOT pinned at `bootCoreId`:
      -- an ordinary syscall on a secondary core writes that core's scheduler
      -- slots, so the boot-core premise is false exactly where the SM3.C.9
      -- migration cares.  A boot-pinned arm here would keep elaborating if
      -- `…_atCore` regressed to the boot form, which is what a claim inventory
      -- exists to prevent.
      --
      -- WS-LS LS2.1: over the pair, with no `invExt` guard on either side —
      -- the bracket writes the ghost table, so there is no lock write for a
      -- guard to make invisible.  Stated here so a regression that re-grows
      -- the guard is a type error at the inventory.
      ∀ (ctx : LabelingContext) (observer : IfObserver) (S : LockSet) (lockCore : CoreId)
        (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
        (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (st' : SystemState) (c' : CoreId),
        syscallEntryChecked ctx layout executingCore regCount s.kernel = .ok ((), st') →
        projectStateOnCore ctx observer st' c' = projectStateOnCore ctx observer s.kernel c' →
        observableSlotsConfinedToCore s.kernel st' c' →
        lowEquivalent_smp ctx observer
          (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel
          s.kernel
  | .failClosedUnderFineLocks =>
      ∀ (ctx : LabelingContext) (S : LockSet) (lockCore : CoreId)
        (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
        (s : SeLe4n.Kernel.Concurrency.LockedSystemState) (e : KernelError) (L : SecurityLabel),
        syscallEntryChecked ctx layout executingCore regCount s.kernel = .error e →
        ∀ c : CoreId,
          ObservableState.onCore ctx c L
              (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1.kernel
            = ObservableState.onCore ctx c L s.kernel
  | .contentionChannelRegistered =>
      ∀ (maxDelay : Nat) (e : SeLe4n.Kernel.Concurrency.RwLockExecution),
        SeLe4n.Kernel.Concurrency.FairTrace e maxDelay →
        e.initial = RwLockState.unheld →
        ∀ (c : CoreId) (m : AccessMode) (kEnq : Nat),
          (c, m) ∈ (e.stateAt kEnq).waiters →
          kEnq + lockContentionDelayBound maxDelay < e.ops.length →
          e.noCancelIn c kEnq (kEnq + lockContentionDelayBound maxDelay + 1) →
          acceptedCovertChannel_lockContention.modelVisible = false ∧
            acceptedCovertChannel_lockContention.severity = CovertChannelSeverity.medium ∧
            lockContentionCode e c kEnq < lockContentionAlphabet maxDelay ∧
              -- The rate half, in elapsed time.  CC-5's registration is a
              -- bandwidth claim, so the inventory must consume both halves.
              --
              -- WS-LC LC5.8: stated at **the execution's own** cost model, which
              -- is the stronger pin.  The generic form is what proves it, so
              -- consuming this one forces both to exist; consuming the generic
              -- one would have let the execution-level statement — and with it
              -- the `stepCost` field the denomination rests on — be deleted
              -- while this arm kept elaborating.
              (∀ (steps : List Nat), steps.Nodup → (∀ k ∈ steps, k ≤ e.ops.length) →
                (∀ k ∈ steps, 1 ≤ k) →
                ∀ tMin : Nat, e.CostedCriticalSection tMin →
                  steps.length * tMin ≤ e.elapsed 0 e.ops.length)

/-- SM8.D: **the evidence** — every claim discharged by citation.  This
definition is the phase's completeness check: it elaborates only if every claim
has a theorem, and only if that theorem proves *that* claim. -/
def fineLockClaimEvidence : (id : FineLockClaimId) → id.evidenceProp
  | .lockStateInvisible =>
      fun ctx c L s k l₁ l₂ => onCore_lock_indistinguishable ctx c L s k l₁ l₂
  | .readerMultiplicityHidden =>
      fun ctx c L s k r₁ r₂ => readerMultiplicity_not_observable ctx c L s k r₁ r₂
  | .writerExclusionHidden =>
      fun ctx c L s k holder mode =>
        blockedAcquirer_observes_nothing ctx c L s k holder mode
  | .contentionDelayBounded =>
      fun e maxDelay hFair hInit c m kEnq hQueued hWithin hNoCancel =>
        lockContention_delay_bounded e maxDelay hFair hInit c m kEnq hQueued hWithin hNoCancel
  | .integrityUnderLocks =>
      fun _α ctx subject S core action s hAction =>
        bibaIntegrity_underLockSet ctx subject S core action s hAction
  | .authorityIntegrityUnderLocks =>
      fun _α ctx subject S core action s hAction =>
        authorityIntegrity_underLockSet ctx subject S core action s hAction
  | .secureFlowUnderFineLocks =>
      fun ctx observer S lockCore layout executingCore regCount s st' c' hOk hProjOn hConfined =>
        syscallEntryUnderLockSet_preserves_projectionOnCore_atCore ctx observer S lockCore
          layout executingCore regCount s st' c' hOk hProjOn hConfined
  | .failClosedUnderFineLocks =>
      fun ctx S lockCore layout executingCore regCount s e L hDenied =>
        syscallEntryUnderLockSet_failClosed_invisible ctx S lockCore layout executingCore
          regCount s e L hDenied
  | .contentionChannelRegistered =>
      fun maxDelay e hFair hInit c m kEnq hQueued hWithin hNoCancel =>
        ⟨(acceptedCovertChannel_lockContention_bounded maxDelay e hFair hInit c m kEnq hQueued
            hWithin hNoCancel).1,
         (acceptedCovertChannel_lockContention_bounded maxDelay e hFair hInit c m kEnq hQueued
            hWithin hNoCancel).2.1,
         (acceptedCovertChannel_lockContention_bounded maxDelay e hFair hInit c m kEnq hQueued
            hWithin hNoCancel).2.2,
         fun steps hNodup hRange hPos tMin hCost =>
           lockContentionChannel_rate_per_execution_time e tMin hCost steps hNodup hRange
             hPos⟩

/-- SM8.D: the evidence is non-empty at every claim — the sanity check that the
table is inhabited rather than a family of vacuous `True`s. -/
theorem fineLockClaimEvidence_nonempty (id : FineLockClaimId) : Nonempty id.evidenceProp :=
  ⟨fineLockClaimEvidence id⟩

end SeLe4n.Kernel
