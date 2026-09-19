-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.FrozenState
import SeLe4n.Model.FreezeProofs

/-!
# Q7-A: Frozen Kernel Monad and Core Primitives

**STATUS: in the production import chain since `v0.35.60`.**  `SeLe4n.lean`
imports `FrozenOps.Agreement` and `FrozenOps.Invariant`, which reach all five
modules.  The *architectural* switch — `API.lean` running syscall processing over
frozen snapshots — remains deferred and is C.1 row 14 in
`docs/REGISTERED_DEBT.md`; **being in the import chain is not being the dispatch
path**, and a reader must not take one for the other.

AG8-D production decision (H3-PROOF-05): FrozenOps evaluated for H3 promotion.
Decision at the time: **defer as post-1.0 hardening candidate**. Rationale:
1. All 24 per-subsystem operations have preservation theorems (33 total).
2. `FrozenSchedulerState.replenishQueue` present (AG1-E).
3. `FrozenMap` commutativity proofs complete.
4. However, the two-phase architecture requires RPi5 performance benchmarking
   to validate that the freeze→operate→thaw cycle does not exceed the WCRT
   budget on Cortex-A76. This cannot be assessed until a post-1.0 hardware-
   testing workstream is opened.  **Still live** — it gates the dispatch switch,
   and nothing in `v0.35.60` touches it.
5. Zero production consumers — promoting now would add import weight without
   a runtime benefit.  **Refuted at `v0.35.60`, and how it was wrong is worth
   keeping**: it weighed *runtime* benefit only.  The benefit of being in the
   chain is **verification** — the import is what puts a module inside the
   derived domain of the Tier 1 censuses and the production/staging partition
   gate.  Outside it this subsystem was exempt from five of the six censuses and
   from the partition gate entirely, which cost five after-the-fact corrections
   (`v0.35.12`, `v0.35.38`, `v0.35.47`, `v0.35.52`, `v0.35.58`) on a surface
   that carries the **live** `TCB`, `Reply`, `SchedContext` and `IntrusiveQueue`
   records and mirrors the reply and cancellation spines.  Reasoning about
   "import weight" while a differential mirror sat outside every derived gate
   domain weighed the cheap axis and not the expensive one.

These modules implement the frozen-state kernel monad for the **execute**
phase of this project's build → freeze → execute architecture, in which syscall
processing operates on immutable `FrozenSystemState` snapshots.  That is not a
prospective use invented here: `Model.freeze` takes the *builder*'s
`IntermediateState` to a `FrozenSystemState`, and `Platform/Boot.lean`'s
`bootToRuntime_invariantBridge_empty` — *boot to runtime* — already proves
`proofLayerInvariantBundle ist.state ∧ apiInvariantBundle_frozen (freeze ist)`,
a bridge worth proving only if the runtime runs on the frozen representation.
Currently exercised by test suites only: `API.lean` contains no occurrence of
`FrozenOps`, `kernelStateRef` holds a `SystemState`, and `Model.freeze` has no
executable caller anywhere under `SeLe4n/` — every occurrence in `Boot.lean` is
inside a theorem statement.  The freeze is proved and not run.

Integration into the production API layer is a post-1.0 hardening candidate
(registered in `docs/REGISTERED_DEBT.md`, Registered debt index, C.1 row 14).
**Two gates, and until `v0.35.102` only one was written down**: the RPi5
freeze→operate→thaw benchmark data AG8-D point 4 names, *and* the frozen
surface agreeing with the live one on every operation it would dispatch — table
C's open frozen-fidelity row.  A switch taken on benchmark evidence alone would
promote a mirror known to diverge; the correctness gate comes first.
(AE2-E / U-02 / AG8-D)

**Subsystem status:** FrozenOps has no production *caller* — the kernel API
(`API.lean`) does not dispatch through it — but it is in the production import
chain since `v0.35.60`, so it is not outside the gates' derived domains.  The
distinction is the point: a module can be checked by everything and called by
nothing, and conflating "no caller" with "not production" is what exempted this
surface from five of the six Tier 1 censuses.  It remains **architectural
validation infrastructure** for the two-phase (builder→frozen) state model, and
it is also the live kernel's differential mirror:

- `FrozenKernel` monad validates that `FrozenMap` lookups/mutations are
  expressible as pure functions with `FrozenSystemState`.
- Commutativity proofs (`Commutativity.lean`) validate `FrozenMap.set`/`get?`
  round-trip correctness, supporting the `FreezeProofs` module's argument.
- `Operations.lean` demonstrates that all 12 per-subsystem operations can be
  expressed purely over the frozen representation.

When the H3 hardware binding integrates runtime execution, FrozenOps is the
intended runtime monad. Until then, it serves as proof-of-concept infrastructure.

Defines the execution-phase monad for operating on `FrozenSystemState`.
All lookups use `FrozenMap.get?` (index lookup + array access) and value
mutations use `FrozenMap.set` (in-place array update at existing index).

The index map is immutable for every operation that only changes values, which
is all of them but one: a wake has to enqueue into a bucket the snapshot may not
hold, because the live `ensureRunnable` creates it. `frozenEnsureRunnable` uses
`FrozenMap.insert`, which appends rather than refusing (PR #873 round 17); every
stored index stays in range by `FrozenMap.insert_preserves_wellFormed`. All
`Fin` accesses are within bounds by construction. No fuel is needed.

## Design

- `FrozenKernel α`: state monad over `FrozenSystemState` with `KernelError`
- `frozenLookupObject`: typed object lookup via `FrozenMap.get?`
- `frozenStoreObject`: value-only mutation via `FrozenMap.set`
- `frozenLookupTcb`: typed TCB extraction with sentinel check
- `frozenStoreTcb`: convenience wrapper for TCB updates
-/

namespace SeLe4n.Kernel.FrozenOps

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.RadixTree

-- ============================================================================
-- Q7-A: FrozenKernel Monad
-- ============================================================================

/-- Q7-A: Execution-phase kernel monad operating on `FrozenSystemState`.
Same `KernelM` shape as the builder-phase `Kernel`, but over frozen state. -/
abbrev FrozenKernel := KernelM FrozenSystemState KernelError

-- ============================================================================
-- Q7-A: Core Lookup Primitives
-- ============================================================================

/-- Q7-A: Look up a frozen kernel object by ObjId.
Uses `FrozenMap.get?` — one hash in indexMap + one array access. -/
def frozenLookupObject (id : SeLe4n.ObjId) : FrozenKernel FrozenKernelObject :=
  fun st =>
    match st.getObject? id with
    | some obj => .ok (obj, st)
    | none => .error .objectNotFound

/-- Q7-A: Look up a TCB by ThreadId in frozen state.
Mirrors `lookupTcb` from builder phase: sentinel check + type match. -/
def frozenLookupTcb (st : FrozenSystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  if tid.isReserved then none else st.getTcb? tid

/-- Q7-A: Look up an endpoint by ObjId in frozen state. -/
def frozenLookupEndpoint (st : FrozenSystemState) (epId : SeLe4n.ObjId) : Option Endpoint :=
  st.getEndpoint? epId

/-- Q7-A: Look up a notification by ObjId in frozen state. -/
def frozenLookupNotification (st : FrozenSystemState) (nId : SeLe4n.ObjId) : Option Notification :=
  st.getNotification? nId

/-- Q7-A: Look up a frozen CNode by ObjId in frozen state. -/
def frozenLookupCNode (st : FrozenSystemState) (cnId : SeLe4n.ObjId) : Option FrozenCNode :=
  st.getCNode? cnId

-- ============================================================================
-- Q7-B: Core Mutation Primitives (Value-Only)
-- ============================================================================

/-- **PR #897 review: the frozen object table's one checked write.**

`Model.withObjectStored`'s counterpart, and it returns an `Except` where the live
one is total: `storeObject` cannot fail, while a frozen key the freeze did not
capture has no slot to write.

`FrozenMap.set` answers `none` for such a key, and every frozen transition that
wrote an object had that `match` inlined -- 31 executable occurrences across 22
declarations, invisible to `STORE_WRITE_CODE`'s enforced zero because the census's
method branch named `insert` and `erase` and not `set`.  A spelling the gate does
not recognise is not a licence to keep it: the live surface routes every write
through `storeObject` / `withObjectStored` / `rewriteObject`, and this is the
frozen counterpart of that discipline.

**State level, deliberately.**  A map-level primitive would have served the two
helpers that chain writes on the table itself -- and its own raw `set` would then
sit on a bare `FrozenMap` parameter, which the census keys on `.objects` and so
cannot see.  Moving 31 writes into a helper the scanner is blind to is *choosing
a spelling to evade a metric*, which is the defect this cut exists to close; the
two helpers take a state instead. -/
def frozenWithObjectStored (st : FrozenSystemState) (id : SeLe4n.ObjId)
    (obj : FrozenKernelObject) : Except KernelError FrozenSystemState :=
  match st.objects.set id obj with
  | some objects' => .ok { st with objects := objects' }
  | none => .error .objectNotFound

/-- Q7-B: Store a frozen kernel object at an existing key.

The `FrozenKernel` wrapper over `frozenWithObjectStored`, as the live
`storeObject` is the monadic spelling of `withObjectStored`.  The raw
`FrozenMap.set` is in `frozenWithObjectStored` and nowhere else. -/
def frozenStoreObject (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    : FrozenKernel Unit :=
  fun st =>
    match frozenWithObjectStored st id obj with
    | .ok st' => .ok ((), st')
    | .error e => .error e

/-- The **total** in-place rewrite, mirroring the live `rewriteObject`.

`FrozenMap.insert` is `set` with an append fallback, so on a key the store
already holds the two agree definitionally; where they part is an *absent* key,
which `insert` appends and this leaves alone.  A frozen transition that has
already resolved its object reaches a present key by construction, so the
identity arm is unreachable from every caller -- and it is the right arm to
have, because a rewrite that silently created an object would be a write the
live surface cannot perform.

This exists so a total transition need not reach for the raw table: before it,
`frozenUpdatePipBoost` spelled its write `st.objects.insert`, which is the same
write in a spelling the census's `set`-only branch did not recognise, so it sat
past an enforced zero as a *registered primitive* -- a transition wearing a
primitive's exemption. -/
def frozenRewriteObject (st : FrozenSystemState) (id : SeLe4n.ObjId)
    (obj : FrozenKernelObject) : FrozenSystemState :=
  match frozenWithObjectStored st id obj with
  | .ok st' => st'
  | .error _ => st

-- ============================================================================
-- The frozen write's frame -- stated once, at the write
-- ============================================================================

/-! ### What a frozen store changes

`frozenWithObjectStored` is the frozen surface's one raw `FrozenMap.set`, so
"which fields does a frozen store change" is a question about **it**, not about
each operation built from it.  Before the raw writes were collapsed onto it the
question had **twelve** answers: eleven proofs across `Core`, `Commutativity`
and `Invariant` each `unfold`ed a composite down to `FrozenMap.set` and
case-split on it, and a twelfth -- `frozenStoreObject_extracts_state` -- said
exactly this, `private`, in `Invariant.lean`, downstream of every one of the
eleven that could not see it.  *When a question has one owner and an asker that
cannot see it, the owner is in the wrong layer.*

The three lemmas below are that owner, beside the write they are about.
`_ok` is the sharp reading (the stored table is `set`'s own output),
`_only_modifies_objects` the frame consumers want, and `_trans` what lets a
composite that chains stores inherit the frame instead of re-deriving it by
destructuring its own body -- which is what coupled the old proofs to how many
branches a body happened to have. -/

/-- The sharp reading of a successful frozen store: the post-state is the
pre-state with `objects` replaced by `FrozenMap.set`'s own output. -/
theorem frozenWithObjectStored_ok
    {st st' : FrozenSystemState} {id : SeLe4n.ObjId} {obj : FrozenKernelObject}
    (hOk : frozenWithObjectStored st id obj = .ok st') :
    ∃ objects', st.objects.set id obj = some objects' ∧
      st' = { st with objects := objects' } := by
  unfold frozenWithObjectStored at hOk
  cases hSet : st.objects.set id obj with
  | some objects' =>
    rw [hSet] at hOk
    exact ⟨objects', rfl, by injection hOk with hEq; exact hEq.symm⟩
  | none => rw [hSet] at hOk; simp at hOk

/-- A successful frozen store changes `objects` and nothing else. -/
theorem frozenWithObjectStored_only_modifies_objects
    {st st' : FrozenSystemState} {id : SeLe4n.ObjId} {obj : FrozenKernelObject}
    (hOk : frozenWithObjectStored st id obj = .ok st') :
    ∃ objects', st' = { st with objects := objects' } := by
  obtain ⟨objects', _, hSt⟩ := frozenWithObjectStored_ok hOk
  exact ⟨objects', hSt⟩

/-- The total rewrite changes `objects` and nothing else -- on either arm. -/
theorem frozenRewriteObject_only_modifies_objects
    (st : FrozenSystemState) (id : SeLe4n.ObjId) (obj : FrozenKernelObject) :
    ∃ objects', frozenRewriteObject st id obj = { st with objects := objects' } := by
  unfold frozenRewriteObject
  cases hStore : frozenWithObjectStored st id obj with
  | ok st1 => obtain ⟨o, hSt⟩ := frozenWithObjectStored_only_modifies_objects hStore; exact ⟨o, hSt⟩
  | error e => exact ⟨st.objects, rfl⟩

/-- A state changes only `objects` from itself -- the base case a store chain
unwinds to. -/
theorem frozenOnlyObjects_rfl {st : FrozenSystemState} :
    ∃ objects', st = { st with objects := objects' } :=
  ⟨st.objects, rfl⟩

/-- Changing only `objects` composes, so an operation that chains stores
inherits the frame rather than re-deriving it from its own body. -/
theorem frozenOnlyObjects_trans {st st1 st2 : FrozenSystemState}
    (h1 : ∃ objects', st1 = { st with objects := objects' })
    (h2 : ∃ objects', st2 = { st1 with objects := objects' }) :
    ∃ objects', st2 = { st with objects := objects' } := by
  obtain ⟨_, rfl⟩ := h1
  obtain ⟨o2, rfl⟩ := h2
  exact ⟨o2, rfl⟩

/-- The monadic wrapper's sharp reading. -/
theorem frozenStoreObject_ok
    {st st' : FrozenSystemState} {id : SeLe4n.ObjId} {obj : FrozenKernelObject}
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    ∃ objects', st.objects.set id obj = some objects' ∧
      st' = { st with objects := objects' } := by
  unfold frozenStoreObject at hOk
  cases hStore : frozenWithObjectStored st id obj with
  | ok st1 =>
    rw [hStore] at hOk
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hOk
    exact hOk ▸ frozenWithObjectStored_ok hStore
  | error e => rw [hStore] at hOk; simp at hOk

/-- Q7-B: Update a TCB in frozen state. Convenience wrapper around
`frozenStoreObject` that wraps the TCB in `FrozenKernelObject.tcb`. -/
def frozenStoreTcb (tid : SeLe4n.ThreadId) (tcb : TCB)
    : FrozenKernel Unit :=
  frozenStoreObject tid.toObjId (.tcb tcb)

/-- Q7-B: Update an endpoint in frozen state. -/
def frozenStoreEndpoint (epId : SeLe4n.ObjId) (ep : Endpoint)
    : FrozenKernel Unit :=
  frozenStoreObject epId (.endpoint ep)

/-- Q7-B: Update a notification in frozen state. -/
def frozenStoreNotification (nId : SeLe4n.ObjId) (n : Notification)
    : FrozenKernel Unit :=
  frozenStoreObject nId (.notification n)

-- ============================================================================
-- AK8-G (DS-M01): Variant-kind-checked frozen store wrappers
-- ============================================================================

/-! ### AK8-G (DS-M01) — Typing Disjointness for Frozen Stores

`frozenStoreObject` delegates to `FrozenMap.set`, which overwrites the stored
value at an existing key regardless of variant. A bug-injected (or fuzz-
generated) call like `frozenStoreTcb tid (some TCB)` on a key that holds
a `.schedContext` / `.endpoint` / `.notification` would silently corrupt
the object store's variant discipline.

The production invariant `lifecycleObjectTypeLockstep` (AM4/AL6-C) rules
this out at the proof layer, but FrozenOps has no such invariant on its
`FrozenSystemState`. This matters because FrozenOps is the test-only
two-phase-architecture validation layer (W3-G / AG8-D) and a cross-variant
overwrite would produce inconsistent frozen-state fixtures without an
obvious failure mode.

These `*Checked` wrappers pre-validate the variant at the target key via
the corresponding `frozenLookup*` helper and return `.error .objectNotFound`
on a kind mismatch (matching the `frozenStoreObject` error kind for
consistency with the rest of the FrozenOps error surface).

**Scope:** FrozenOps is TEST-ONLY (audit §7.7 — confirmed NOT in the
production import chain). AK8-G is a hardening fix for the test surface.
-/

/-- AK8-G (DS-M01): Kind-checked TCB store. Rejects writes when the target
key either does not exist or does not currently hold a `.tcb` variant. -/
def frozenStoreTcbChecked (tid : SeLe4n.ThreadId) (tcb : TCB)
    : FrozenKernel Unit :=
  fun st =>
    match frozenLookupTcb st tid with
    | some _ => frozenStoreTcb tid tcb st
    | none => .error .objectNotFound

/-- AK8-G (DS-M01): Kind-checked endpoint store. -/
def frozenStoreEndpointChecked (epId : SeLe4n.ObjId) (ep : Endpoint)
    : FrozenKernel Unit :=
  fun st =>
    match frozenLookupEndpoint st epId with
    | some _ => frozenStoreEndpoint epId ep st
    | none => .error .objectNotFound

/-- AK8-G (DS-M01): Kind-checked notification store. -/
def frozenStoreNotificationChecked (nId : SeLe4n.ObjId) (n : Notification)
    : FrozenKernel Unit :=
  fun st =>
    match frozenLookupNotification st nId with
    | some _ => frozenStoreNotification nId n st
    | none => .error .objectNotFound

/-- AK8-G (DS-M01): Soundness — a successful `frozenStoreTcbChecked` call
has the same post-state as the unchecked `frozenStoreTcb`. Allows proofs
that reason about `frozenStoreTcb` to transport to the checked wrapper's
success case. -/
theorem frozenStoreTcbChecked_ok_eq_frozenStoreTcb
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st st' : FrozenSystemState)
    (hOk : frozenStoreTcbChecked tid tcb st = .ok ((), st')) :
    frozenStoreTcb tid tcb st = .ok ((), st') := by
  unfold frozenStoreTcbChecked at hOk
  cases hLookup : frozenLookupTcb st tid with
  | some _ => rw [hLookup] at hOk; exact hOk
  | none => rw [hLookup] at hOk; cases hOk

/-- AK8-G (DS-M01): Soundness — `frozenStoreEndpointChecked` success
agreement with unchecked `frozenStoreEndpoint`. -/
theorem frozenStoreEndpointChecked_ok_eq_frozenStoreEndpoint
    (epId : SeLe4n.ObjId) (ep : Endpoint) (st st' : FrozenSystemState)
    (hOk : frozenStoreEndpointChecked epId ep st = .ok ((), st')) :
    frozenStoreEndpoint epId ep st = .ok ((), st') := by
  unfold frozenStoreEndpointChecked at hOk
  cases hLookup : frozenLookupEndpoint st epId with
  | some _ => rw [hLookup] at hOk; exact hOk
  | none => rw [hLookup] at hOk; cases hOk

/-- AK8-G (DS-M01): Soundness — `frozenStoreNotificationChecked` success
agreement with unchecked `frozenStoreNotification`. -/
theorem frozenStoreNotificationChecked_ok_eq_frozenStoreNotification
    (nId : SeLe4n.ObjId) (n : Notification) (st st' : FrozenSystemState)
    (hOk : frozenStoreNotificationChecked nId n st = .ok ((), st')) :
    frozenStoreNotification nId n st = .ok ((), st') := by
  unfold frozenStoreNotificationChecked at hOk
  cases hLookup : frozenLookupNotification st nId with
  | some _ => rw [hLookup] at hOk; exact hOk
  | none => rw [hLookup] at hOk; cases hOk

/-- **The frozen run queue's insert** (PR #873 round 15), mirroring the live
`ensureRunnable`.

`frozenChooseThread` selects exclusively by folding `scheduler.byPriority` and
filtering on `.ready`.  Until this existed no frozen operation ever wrote that
field, so a thread woken during the frozen phase became `.ready` and stayed
permanently unselectable -- the live `ensureRunnable` put it back in a bucket
and the frozen mirror did not.  The module docstring asserted the opposite and
named `membership`, which `frozenChooseThread` does not read.

**The bucket is created when it is missing** (round 17).  The first cut of this
enqueued through `FrozenMap.set`, which answers `none` for an absent key, and
answered `.illegalState` when the snapshot held no bucket at the woken thread's
priority.  That is not the conservative reading it was written as: the live
`ensureRunnable` creates the bucket through `RunQueue.insert`, so a passive
server blocked at freeze time -- never runnable, therefore never in a bucket --
made the frozen model refuse a transition the kernel performs.  A model that
refuses what the kernel does is wrong in the same way as one that permits what
the kernel refuses.

The fixed key set was a property of `set`, not of the representation, so the
enqueue goes through `FrozenMap.insert`, which appends.  `insert_get?_self`
pins that the thread is then findable and `insert_preserves_wellFormed` that
every stored index stays in range, which is what licensed growing the map.

`membership` is untouched, deliberately: a `FrozenSet` carries `Unit` values, so
its content *is* its key set and cannot change.  `frozenSchedule` already records
it as a read-only census of the population at freeze time. -/
def frozenEnsureRunnable (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    : Except KernelError FrozenSystemState :=
  match frozenLookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      -- **`TCB.boostedPriority`, the live accessor, not a frozen copy of it.**
      -- The frozen store holds the live `TCB` record, so "which bucket does this
      -- thread belong in" has no frozen-specific content and must not have a
      -- frozen-specific answer: the inline `match tcb.pipBoost` that stood here
      -- was one of nine spellings of one expression, and the reversion below
      -- would have needed a tenth.  All of them now read
      -- `Priority.raisedBy` through `Model/Object/Types.lean`.
      let prio : SeLe4n.Priority := tcb.boostedPriority
      let bucket := (st.scheduler.byPriority.get? prio).getD []
      if bucket.contains tid then .ok st
      else
        .ok { st with scheduler := { st.scheduler with
          byPriority := st.scheduler.byPriority.insert prio (bucket ++ [tid]) } }

/-- **The frozen run queue's remove** (PR #873 round 15), mirroring the live
`removeRunnable`: drop the thread from its bucket, and clear `current` if it was
the running thread.

Unlike the insert this cannot fail on a missing key -- a thread absent from every
bucket is already not runnable, so removing it is the identity.  The buckets are
searched rather than indexed by the thread's current priority, because a block
can follow a priority change and the thread must leave the bucket it is actually
in. -/
def frozenRemoveRunnable (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    : FrozenSystemState :=
  let cleared : FrozenSystemState :=
    if st.scheduler.current == some tid then
      { st with scheduler := { st.scheduler with current := none } }
    else st
  cleared.scheduler.byPriority.indexMap.toList.foldl
    (fun acc kv =>
      let bucket := (acc.scheduler.byPriority.get? kv.1).getD []
      if bucket.contains tid then
        match acc.scheduler.byPriority.set kv.1 (bucket.filter (· != tid)) with
        | none => acc
        | some bp => { acc with scheduler := { acc.scheduler with byPriority := bp } }
      else acc)
    cleared

/-- **Is `tid` in any run-queue bucket?** -- the frozen reading of the live
`tid ∈ RunQueue`, which `runQueueOnCore`'s `membership` answers in O(1) and
which has to be a fold here because a `FrozenSet`'s keys are the freeze-time
population rather than the runnable set (`frozenSchedule` records that
`membership` is a read-only census, so it is *not* the queue).

**Queued ANYWHERE, not queued at some particular priority.**  Every live
re-bucketing asks queue membership and then `RunQueue.remove tid`, which takes
the thread out of whichever bucket holds it; looking only in the bucket a
thread's *expected* priority names assumes bucket and effective priority never
drift apart, and a state where they have is exactly the one a re-bucketing has
to repair. -/
def frozenQueuedAnywhere (st : FrozenSystemState) (tid : SeLe4n.ThreadId) : Bool :=
  st.scheduler.byPriority.indexMap.toList.any (fun kv =>
    ((st.scheduler.byPriority.get? kv.1).getD []).contains tid)

/-- **Move `tid` into the bucket `newPrio` names** -- the frozen mirror of the
live `(rq.remove tid).insert tid newPrio`, and the frozen surface's **one**
answer to "a thread's effective priority moved, so which bucket is it in now?".

Three live writers change a run-queue key and every one of them re-buckets:
`updatePipBoostOnCore` (the inherited boost), `migrateRunQueueBucketOnCore` (the
base priority, which `applyPriorityChangeOnCore` composes) and
`schedContextBind`'s Z5-G3 step (the base priority a bind propagates from the
reservation).  The frozen surface had this spelled **once**, inline in
`frozenUpdatePipBoost`, so only the boost half was answered -- and
`TCB.boostedPriority` is `priority.raisedBy pipBoost`, so a *base* write moves
the key exactly as a boost write does.  Reported on PR #897 against
`frozenSchedContextBind` and `frozenWriteBasePriority`, both of which wrote a
base priority and left the thread where it was: `frozenChooseThread` folds
`byPriority`, so the frozen kernel went on selecting the thread at the band the
write had just removed, and a later `frozenEnsureRunnable` -- which appends when
the thread is absent from the bucket for its *new* priority -- would have left it
in **two**.  That is this project's *one question answered in two places* shape
with only one of the places ever answering, so the remedy is a shared definition
rather than two per-site patches.

**What this does not own is the guard.**  The live writers disagree there, and
faithfully: `updatePipBoostOnCore` migrates only `if oldPrio != newPrio`, while
`migrateRunQueueBucketOnCore` and the bind migrate whenever the thread is
queued -- and the difference is observable, since `RunQueue.insert` appends, so
a remove-and-reinsert at an unchanged priority moves the thread to its bucket's
tail.  Each caller therefore keeps its own subject's guard and this owns the
mechanics alone.  A caller must also check `frozenQueuedAnywhere` first: an
unqualified call would *insert* a thread that is in no bucket.

**And it does not own which FIELDS a write carries** (PR #897 review,
`v0.35.105`).  Reach for this only where the write moves `boostedPriority`.  A
write of a field that is *not* a run-queue key -- a domain, a binding, an
`ipcState` -- is the surface's ordinary `frozenWithObjectStored`, and a write
that moves both is **two halves**, one through each.  This is the only *named*
TCB write on the frozen surface, so the shape a caller falls into is this one,
and `frozenSchedContextConfigure` fell into it: it mirrored a live operation with
two independently gated halves as a single gate over their union, and a
domain-only reconfiguration then re-bucketed a queued thread to its bucket's tail
at an unchanged key.  Two live questions given one frozen answer is the dual of
this project's *one question, two answers* shape, and it reads as correct because
the shared answer is the right one -- for the half that asked it.

Empty buckets are left behind rather than erased, which is the convention
`frozenRemoveRunnable` already follows: `frozenRunAgrees` compares
`(get? prio).getD []` at every key present on either side, so an empty frozen
bucket and an absent live key agree. -/
def frozenRebucketRunnable (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    (newPrio : SeLe4n.Priority) : FrozenSystemState :=
  let dropped := st.scheduler.byPriority.indexMap.toList.foldl
    (fun bp kv =>
      let bucket := (bp.get? kv.1).getD []
      if bucket.contains tid then bp.insert kv.1 (bucket.filter (· != tid)) else bp)
    st.scheduler.byPriority
  let newBucket := (dropped.get? newPrio).getD []
  { st with scheduler := { st.scheduler with
      byPriority := dropped.insert newPrio (newBucket ++ [tid]) } }

/-- **Write a TCB and re-bucket it if its effective priority moved** -- the shape
the two base-priority writers share, and the one a new frozen priority writer
reaches for.

The bucket key is `after.boostedPriority` -- the live accessor, which
`frozenEnsureRunnable` and `frozenChooseThread` already read, so "which bucket
does this thread belong in" keeps one answer on this surface.  It is read off the
record being *written* rather than looked up afterwards, which is the stronger
spelling: a lookup could read a record some later write had moved.

The guard is `migrateRunQueueBucketOnCore`'s, not `updatePipBoostOnCore`'s:
**queue membership alone, with no `oldPrio != newPrio` condition**, because that
is what the live base-priority writers do -- and the difference is observable
rather than cosmetic.  `RunQueue.insert` appends (`bucket ++ [tid]`), so the
live remove-and-reinsert moves the thread to its bucket's *tail* even at an
unchanged key; a frozen mirror that short-circuited there would keep the thread
at its old position, and `frozenRunAgrees` compares buckets as **lists**.  A
`.tcbSetPriority` that writes a thread's current priority reaches exactly that
case.

The caller that needs the guarded form (`frozenUpdatePipBoost`, mirroring
`updatePipBoostOnCore`) composes `frozenQueuedAnywhere` and
`frozenRebucketRunnable` itself rather than reaching for this. -/
def frozenWriteTcbRebucketed (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    (after : TCB) : Except KernelError FrozenSystemState :=
  match frozenWithObjectStored st tid.toObjId (.tcb after) with
  | .error e => .error e
  | .ok st' =>
      if frozenQueuedAnywhere st' tid then
        .ok (frozenRebucketRunnable st' tid after.boostedPriority)
      else .ok st'

-- ============================================================================
-- **Frozen priority inheritance** (PR #895 review round 15)
-- ============================================================================

/-- **The threads directly blocked on `tid` via Reply IPC** -- `waitersOf`'s
frozen counterpart (`Scheduler/PriorityInheritance/BlockingGraph.lean`).

The live version folds `objectIndex`; this one folds the frozen object map,
which is the same population by construction (`Model.freeze` copies every
object).  A thread is a waiter of `tid` exactly when its `ipcState` records
`tid` as the server it is blocked on. -/
def frozenWaitersOf (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    : List SeLe4n.ThreadId :=
  st.objects.fold (init := []) fun acc _id obj =>
    match obj with
    -- `TCB.blockingServer?` is the live reading of the blocking edge, shared
    -- with `waitersOf` and `blockingServer`, so the frozen walk and the live one
    -- provably follow the same edges rather than two matches that agree today.
    | .tcb tcb => if tcb.blockingServer? == some tid then tcb.tid :: acc else acc
    | _ => acc

/-- **The highest effective priority among `tid`'s waiters**, or `none` when it
has none -- `computeMaxWaiterPriority`'s frozen counterpart.

"Effective" is `TCB.boostedPriority`, the same accessor the frozen run queue
buckets by, so a boost computed here and the bucket it lands a thread in cannot
disagree.  (The live version reads `effectiveSchedParams`, which additionally
consults the waiter's SchedContext; this surface has no scheduling-parameter
resolution and buckets by the TCB alone, so consulting one here would be a
*second* answer to the question `frozenEnsureRunnable` already decides.) -/
def frozenComputeMaxWaiterPriority (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    : Option SeLe4n.Priority :=
  (frozenWaitersOf st tid).foldl (fun acc waiterTid =>
    match st.getTcb? waiterTid with
    | some waiterTcb =>
        let prio := waiterTcb.boostedPriority
        match acc with
        | none => some prio
        | some curMax => some ⟨Nat.max curMax.val prio.val⟩
    | none => acc) none

/-- **The server `tid` is blocked on**, if any -- `blockingServer`'s frozen
counterpart.  One step of the blocking graph, read off the thread's own
`ipcState`. -/
def frozenBlockingServer (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    : Option SeLe4n.ThreadId :=
  (st.getTcb? tid).bind TCB.blockingServer?

/-- **Recompute `tid`'s inherited boost from its current waiters, and re-bucket
it** -- `updatePipBoost`'s frozen counterpart.

Two halves, and the second is why this cannot be a bare field write.  The frozen
run queue is keyed by `TCB.boostedPriority`, so a thread whose boost changes
while it sits in a bucket is in the *wrong* bucket -- and a later
`frozenEnsureRunnable` would not repair it: that function appends when the
thread is absent from the bucket for its new priority, so the thread would end
up in **two**.  The live `updatePipBoost` migrates for exactly this reason.

The migration is conditional on the thread actually being in a bucket, mirroring
the live `if tid ∈ runQueueOnCore` -- and it is deliberately not spelled as
`frozenRemoveRunnable` followed by `frozenEnsureRunnable`, because the removal
also clears `current`, which the live migration does not do.  A running thread's
current slot is not a run-queue bucket and a priority change must not vacate
it. -/
def frozenUpdatePipBoost (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    : FrozenSystemState :=
  match st.getTcb? tid with
  | none => st
  | some tcb =>
      let newBoost := frozenComputeMaxWaiterPriority st tid
      if tcb.pipBoost == newBoost then st
      else
        let tcb' := { tcb with pipBoost := newBoost }
        let oldPrio := tcb.boostedPriority
        let newPrio := tcb'.boostedPriority
        let st' : FrozenSystemState :=
          frozenRewriteObject st tid.toObjId (.tcb tcb')
        -- **The mechanics are `frozenRebucketRunnable`; the guard is this
        -- operation's own.**  Up to `v0.35.100` the fold and the membership scan
        -- were spelled inline here, which made this the *only* frozen writer
        -- that re-bucketed at all -- so `frozenSchedContextBind` and
        -- `frozenWriteBasePriority`, which move the same key through
        -- `TCB.priority` rather than through `pipBoost`, left the thread in the
        -- band their own write had removed (PR #897 review).  The guard stays
        -- here because the live writers disagree about it and faithfully:
        -- `updatePipBoostOnCore` migrates only `if oldPrio != newPrio`, where
        -- `migrateRunQueueBucketOnCore` and the bind migrate whenever the thread
        -- is queued.
        --
        -- `frozenQueuedAnywhere` asks membership in **any** bucket, which is
        -- what the live `tid ∈ runQueueOnCore` plus `RunQueue.remove` does:
        -- looking only in the bucket `oldPrio` names assumes a thread's bucket
        -- always equals its effective priority, and a state where the two have
        -- drifted apart is exactly the one a reversion has to repair -- on such
        -- a state the thread was left where it was while the live kernel moved
        -- it, which the operation-level differential (FO-041) caught on its
        -- first run.
        if oldPrio == newPrio || !frozenQueuedAnywhere st' tid then st'
        else frozenRebucketRunnable st' tid newPrio

/-- **Revert priority inheritance for `tid` and the chain above it** --
`revertPriorityInheritance`'s frozen counterpart, and the step the frozen reply
was missing.

Structurally identical to propagation, as the live pair is: `frozenUpdatePipBoost`
always recomputes from the *current* waiters, so unblocking a caller and blocking
a new one are the same operation on the server's boost.

Fuel defaults to the object count, which bounds any acyclic chain, and running
out returns the state reached so far -- the live function's own semantics. -/
def frozenRevertPriorityInheritance (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    (fuel : Nat := st.objects.size) : FrozenSystemState :=
  match fuel with
  | 0 => st
  | fuel' + 1 =>
      let st' := frozenUpdatePipBoost st tid
      -- The chain topology is read from the PRE-update state, as the live walk
      -- does: `frozenUpdatePipBoost` writes `pipBoost` and a bucket, never an
      -- `ipcState`, so the blocking graph is unchanged either way.
      match frozenBlockingServer st tid with
      | some nextServer => frozenRevertPriorityInheritance st' nextServer fuel'
      | none => st'

/-- **Link a dequeued caller to the server's reply object** (PR #873 round 17),
mirroring `SystemState.linkCallerReply`.

Both single-use barriers are kept, because both are what make the link
unforgeable: a Reply already naming a caller is refused (`linkReply`'s barrier),
and a caller already holding a reply object is refused, else the old Reply is
orphaned with a stale `caller` and a later reply cap could resolve to it.

The frozen receive needs this because a `.blockedOnCall` sender does not become
runnable at rendezvous — it becomes `.blockedOnReply`, holding a link the reply
transition later consumes. Without it the frozen receive woke the caller, which
is a transition the live kernel never performs. -/
def frozenLinkCallerReply (st : FrozenSystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : Except KernelError FrozenSystemState :=
  match st.getObject? rid.toObjId with
  | some (.reply r) =>
      -- **`Reply.isFree`, not `caller.isNone`** — the one spelling of "this
      -- Reply may be linked to a new caller", which reads *both* stack links as
      -- well.  This guard read the caller alone, so a frame still on a live
      -- reply stack was linkable here while `Model.linkReply` refuses it; that
      -- is the fifth guard deciding one question differently, and `isFree`'s own
      -- docstring records the last time this tree paid for it.
      if r.isFree then
        match frozenWithObjectStored st rid.toObjId
            (.reply { r with caller := some caller }) with
        | .error e => .error e
        | .ok st1 =>
            match frozenLookupTcb st1 caller with
            | none => .error .objectNotFound
            | some tcb =>
                if tcb.replyObject.isNone then
                  frozenWithObjectStored st1 caller.toObjId
                    (.tcb { tcb with replyObject := some rid })
                else .error .replyCapInvalid
      else .error .replyCapInvalid
  | _ => .error .replyCapInvalid

/-- **WS-HP HP8.1, frozen mirror**: the frame *below* the cut, when there is one
that reciprocates.

`spliceFrameBelow?`'s counterpart, clause for clause, and the **four declining
arms are load-bearing here for the same reason they are live**: the removal's
`…OrSelf` fold turns a *refusal* into the identity, and that is sound only
because a refusal means nothing links down to the cut frame, so the consume that
follows breaks no reciprocity.  A below-side refusal folded to the identity would
leave a reciprocating frame above still naming a frame whose caller has been
cleared.  So not named, naming the frame above, not resolving and not
reciprocating all mean *not followed*, and the removal degenerates to the sever
there — which is exactly what this surface did before HP8.

`below ≠ above` is a check rather than a consequence, as live: a frame whose
`prev` and `next` named one neighbour would have two of the three stores collide
at one key, leaving a self-referential frame no walk can leave.

The cut frame's record is an **argument** rather than re-read, because the one
caller has already resolved it and read the `next` that named `above`: reading it
again would answer one question twice. -/
def frozenSpliceFrameBelow? (st : FrozenSystemState) (rid : SeLe4n.ReplyId)
    (r : SeLe4n.Kernel.Reply) (above : SeLe4n.ReplyId) :
    Option (SeLe4n.ReplyId × SeLe4n.Kernel.Reply) :=
  match r.prev with
  | none => none
  | some below =>
    if below == above then none
    else
      match st.getReply? below with
      | none => none
      | some b => if b.next != some (.frame rid) then none else some (below, b)

/-- **WS-HP HP8.1, frozen mirror**: the removal's store step — **three** stores
when there is a frame below, one when there is not.

`spliceReplyFrameStores`'s counterpart.  The third store is not optional and the
live docstring says why: without `rid.prev := none` the cut frame keeps a `prev`
that nothing below names back, which falsifies the chain's `prevLinkReciprocal`
at the cut frame.  It is seL4's `reply_unlink` downward half, and on this surface
it costs nothing either — the frozen store writes by key and the cut frame's key
is already written by the consume that follows. -/
def frozenSpliceReplyFrameStores (st : FrozenSystemState) (rid above : SeLe4n.ReplyId)
    (r a : SeLe4n.Kernel.Reply) : Except KernelError FrozenSystemState :=
  match frozenSpliceFrameBelow? st rid r above with
  | none =>
    frozenWithObjectStored st above.toObjId (.reply { a with prev := none })
  | some (below, b) =>
    match frozenWithObjectStored st above.toObjId
        (.reply { a with prev := some below }) with
    | .error e => .error e
    | .ok st1 =>
      match frozenWithObjectStored st1 below.toObjId
          (.reply { b with next := some (.frame above) }) with
      | .error e => .error e
      | .ok st2 =>
        frozenWithObjectStored st2 rid.toObjId (.reply { r with prev := none })

/-- **WS-HP HP8, frozen mirror**: splice the frame `rid` out of its reply stack.

`spliceReplyFrameOut`'s counterpart, and the frozen surface's whole reason for
carrying one: `FrozenKernelObject.reply` holds the **live** `SeLe4n.Kernel.Reply`
and `Model.freeze` copies a live state's Reply objects verbatim, so a frozen state
taken mid-call-chain holds a doubly linked reply stack exactly as the live one
does.  Consuming a frame's `caller` while leaving it on that stack falsifies the
chain's `prevLinkReciprocal` here for the same reason it did live.

**This was `frozenDetachReplyFrameAbove` until HP8, and it severed.**  HP6.1's
rule is why the rename waited for this cut rather than arriving with the live
one: a `frozenDetach…` beside a live `splice…` reads as the *schedule* (this
surface still severs, HP8 is the cut that changes it) where a `frozenSplice…`
whose body severs reads as a drift.  The name and the body move together.

Clause for clause with the live removal: no Reply at `rid`, and a frame that
heads a context or sits at the top, are the identity; an upward `.frame` link
whose target is missing is `.objectNotFound`; and a target that does **not**
reciprocate is `.invalidArgument` rather than a write, which is what confines
the stores to the genuine frame above.  So the refusal set is unchanged from
the sever's, and every refusal this surface's scenarios exercise carries. -/
def frozenSpliceReplyFrameOut (st : FrozenSystemState) (rid : SeLe4n.ReplyId) :
    Except KernelError FrozenSystemState :=
  match st.getReply? rid with
  | none => .ok st
  | some r =>
    match r.next with
    | some (.frame above) =>
      match st.getReply? above with
      | none => .error .objectNotFound
      | some a =>
        if a.prev != some rid then .error .invalidArgument
        else frozenSpliceReplyFrameStores st rid above r a
    | _ => .ok st

/-- **WS-HP HP8, frozen mirror**: the removal folded to the identity on refusal.

`spliceReplyFrameOutOrSelf`'s counterpart, and the two make the same reading: a
non-reciprocating upward link means "nothing above me on my stack", which the
chain relation permits by design since it is stated downward. -/
def frozenSpliceReplyFrameOutOrSelf (st : FrozenSystemState) (rid : SeLe4n.ReplyId) :
    FrozenSystemState :=
  (frozenSpliceReplyFrameOut st rid).toOption.getD st

/-- **WS-HP HP8.1: where there is nothing below to splice to, the splice IS the
sever** — the frozen counterpart of `spliceReplyFrameOut_eq_sever_of_no_frame_below`.

This is the measurement that the flip is confined to the shape it is about: on a
frame whose `prev` names nothing that reciprocates — every reply in a frozen state
with no call chain, and every *bottom* cut frame — the new body is the retired
`frozenDetachReplyFrameAbove` verbatim, so no differential scenario that passed
before HP8 can change its answer for any other reason. -/
theorem frozenSpliceReplyFrameStores_eq_sever_of_no_frame_below
    {st : FrozenSystemState} {rid above : SeLe4n.ReplyId} {r a : SeLe4n.Kernel.Reply}
    (h : frozenSpliceFrameBelow? st rid r above = none) :
    frozenSpliceReplyFrameStores st rid above r a =
      frozenWithObjectStored st above.toObjId (.reply { a with prev := none }) := by
  unfold frozenSpliceReplyFrameStores
  rw [h]

/-- **WS-HP HP8.1, frozen mirror**: the scheduling context the frame `rid`
**heads**, if it heads one.

`replyFrameHeadContext?`'s counterpart, clause for clause, and it asks the same
*reciprocal* question: the frame's upward link must name the context and the
context's `scReply` must name the frame back.  A one-sided link is a stale
reference over a re-used Reply, and reading it as a head is what would hand a
scheduling context to a thread that is owed nothing.

This exists because HP4 made the **live** `.reply` operation head-driven while
this surface still read the recorded server's `.donated` binding.  The two
triggers coincide on every state `severAtCut` leaves and part company on the
states HP6's splice creates, so a binding-driven mirror of a head-driven
operation is this project's *one question answered in two places* with the
divergence already scheduled. -/
def frozenReplyFrameHeadContext? (st : FrozenSystemState) (rid : SeLe4n.ReplyId) :
    Option SeLe4n.SchedContextId :=
  match st.getReply? rid with
  | none => none
  | some r =>
    match r.next with
    | some (.head scId) =>
      match st.getSchedContext? scId with
      | none => none
      | some sc => if sc.scReply == some rid then some scId else none
    | _ => none

/-- **WS-HP HP8.1, frozen mirror**: the context the frame `rid` heads, **and the
thread currently holding it**.

`replyFrameHeadHolder?`'s counterpart.  The holder is the context's own
`boundThread`, which is the thread the pop takes the reservation *from* — not the
replier, who on a delegated reply capability holds nothing.  A context heading a
frame with no bound thread answers `none` rather than a partial pair: there is
nobody to unbind, so there is no pop to perform. -/
def frozenReplyFrameHeadHolder? (st : FrozenSystemState) (rid : SeLe4n.ReplyId) :
    Option (SeLe4n.SchedContextId × SeLe4n.ThreadId) :=
  match frozenReplyFrameHeadContext? st rid with
  | none => none
  | some scId =>
    match (st.getSchedContext? scId).bind (·.boundThread) with
    | none => none
    | some holder => some (scId, holder)

/-- **WS-RM, frozen mirror**: the reply-stack head the context `scId` owns.

`donationHeadOf?`'s counterpart, clause for clause: a context heading no stack
answers `none`; a recorded head that resolves to no Reply is `.objectNotFound`;
and a head whose own upward link does not name **this** context is
`.invalidArgument` rather than a value, so a stale `scReply` commits nothing. -/
def frozenDonationHeadOf? (st : FrozenSystemState) (scId : SeLe4n.SchedContextId)
    (sc : SeLe4n.Kernel.SchedContext) :
    Except KernelError (Option (SeLe4n.ReplyId × SeLe4n.Kernel.Reply)) :=
  match sc.scReply with
  | none => .ok none
  | some rid =>
    match st.getReply? rid with
    | some r =>
      if r.next != some (.head scId) then .error .invalidArgument
      else .ok (some (rid, r))
    | none => .error .objectNotFound

/-- **WS-RM, frozen mirror**: may this pop hand the context to `newOwner?`?

`outerCallerAcceptable`'s counterpart.  `none` -- the bottom of the stack -- is
always acceptable; a named outer caller must be neither of the two threads the
pop rewrites, must hold no binding of its own, and must be waiting on its reply.
Fail-closed on an unresolvable thread, since the pop mints a binding for it. -/
def frozenOuterCallerAcceptable (st : FrozenSystemState)
    (serverTid originalOwner : SeLe4n.ThreadId) :
    Option SeLe4n.ThreadId → Bool
  | none => true
  | some outer =>
    outer != originalOwner && outer != serverTid &&
      (match st.getTcb? outer with
       | none => false
       | some outerTcb =>
         outerTcb.schedContextBinding == .unbound &&
           (match outerTcb.ipcState with
            | .blockedOnReply _ _ => true
            | _ => false))

/-- **WS-HP HP4.7, frozen mirror**: may this pop hand the context to
`originalOwner`?

`donationRecipientAcceptable`'s counterpart, and it arrived with the head-driven
trigger for the same reason the live one did: under the binding-driven reading the
recipient was the binding's own recorded owner, so the operation had already seen
it hold nothing; under the head-driven reading it is the **answered caller**, which
no binding this operation reads constrains.  Without the guard a reply would
silently overwrite a reservation that caller had acquired for itself while blocked.

A recipient that does not resolve passes, exactly as on the live side: the
operation's own later lookup reports `.objectNotFound` there, and shadowing that
with `.invalidArgument` would change an error code rather than refuse a write.
`frozenLookupTcb` is the reader, so a reserved id is refused the same way. -/
def frozenDonationRecipientAcceptable (st : FrozenSystemState)
    (originalOwner : SeLe4n.ThreadId) : Bool :=
  match frozenLookupTcb st originalOwner with
  | none => true
  | some tcb => tcb.schedContextBinding == .unbound

/-- **WS-RM, frozen mirror**: the thread one frame below this context's stack
head -- the thread the context is owed to next.

`replyStackOuterCaller?`'s counterpart, and it validates the link it follows for
the same reason: Reply objects are re-linked to new callers, so a stale `prev`
over a reused Reply would hand a scheduling context to an unrelated thread. -/
def frozenReplyStackOuterCaller? (st : FrozenSystemState)
    (scId : SeLe4n.SchedContextId) : Except KernelError (Option SeLe4n.ThreadId) :=
  match st.getSchedContext? scId with
  | none => .error .objectNotFound
  | some sc =>
    match frozenDonationHeadOf? st scId sc with
    | .error e => .error e
    | .ok none => .ok none
    | .ok (some (headRid, head)) =>
      match head.prev with
      | none => .ok none
      | some below =>
        match st.getReply? below with
        | none => .error .objectNotFound
        | some b =>
          if b.next != some (.frame headRid) then .error .invalidArgument
          else
            match b.caller with
            | none => .error .illegalState
            | some outer => .ok (some outer)

/-- **WS-OD (`v0.35.4`), frozen mirror (PR #897 review)**: does this thread's
reply link name a frame on a **live** reply stack?

`replyFrameOnLiveStack`'s counterpart, clause for clause, and it is here because
`frozenSchedContextBind` was missing the refusal it gates.  The frozen store holds
the **live** `Reply` and `SchedContext` records, so the question is the same one
and is asked the same way: reciprocity one step -- the frame or context *above*
must answer this frame -- never `next.isSome`, because a stale upward link is
reachable (the splice's below side degenerates to the sever when the frame below
does not reciprocate) and a thread holding one is owed nothing.

Exact rather than approximate under `donationChainWellFormed`, for the reason the
live guard's docstring gives: `prevLinkReciprocal` and `headTerminates` make a
reciprocated link a link to a frame that is itself on the stack. -/
def frozenReplyFrameOnLiveStack (st : FrozenSystemState) (tcb : TCB) : Bool :=
  match tcb.replyObject with
  | none => false
  | some rid =>
    match st.getReply? rid with
    | none => false
    | some r =>
      match r.next with
      | none => false
      | some (.frame above) =>
        match st.getReply? above with
        | none => false
        | some a => a.prev == some rid
      | some (.head scId) =>
        match st.getSchedContext? scId with
        | none => false
        | some sc => sc.scReply == some rid

/-- **WS-RM, frozen mirror**: clear the popped head's links and re-head the
frame below it onto `scId`.

`storeDonationHeadPop`'s counterpart, and the identity where the context heads
no stack.  Written as its own definition rather than inline in the return below
because the *order* is the content -- the head is cleared before the frame below
is re-headed, so the two writes cannot be read as one. -/
def frozenStoreDonationHeadPop (st : FrozenSystemState) (scId : SeLe4n.SchedContextId) :
    Option (SeLe4n.ReplyId × SeLe4n.Kernel.Reply) → Except KernelError FrozenSystemState
  | none => .ok st
  | some (rid, r) =>
    match st.getReply? rid with
    | none => .error .objectNotFound
    | some h =>
      match frozenWithObjectStored st rid.toObjId
          (.reply { h with prev := none, next := none }) with
      | .error e => .error e
      | .ok st1 =>
        match r.prev with
        | none => .ok st1
        | some below =>
          match st1.getReply? below with
          | none => .error .objectNotFound
          | some b =>
            frozenWithObjectStored st1 below.toObjId
              (.reply { b with next := some (.head scId) })

/-- **WS-RM, frozen mirror**: hand a donated scheduling context back.

`returnDonatedSchedContext`'s counterpart -- the four object writes, in the live
order: the SchedContext rebinds to `originalOwner` and re-points `scReply` at the
frame below its head, the popped head's links are cleared and that frame
re-headed, the owner takes `donationReturnBinding` (the **live** function, so the
two surfaces cannot disagree about which binding a return mints), and the server
goes `.unbound`.  All three of the live guards come with it: the context must
really be bound to the server, the outer caller must be acceptable before it is
handed one, and -- since WS-HP HP4.7 made this surface's pop head-driven -- so
must the recipient.  The order is the live order, and all three precede every
write.

**`scThreadIndex` is deliberately not maintained**, and that is this surface's
existing answer rather than an omission here: no frozen operation writes it --
`frozenSchedContextBind` and `frozenSchedContextUnbind` rebind without touching
it -- and `frozenStateAgrees` does not compare it.  Becoming its only writer
would be a second answer to a question the surface has already settled. -/
def frozenReturnDonatedSchedContext (st : FrozenSystemState)
    (serverTid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId) (newOwner? : Option SeLe4n.ThreadId) :
    Except KernelError FrozenSystemState :=
  match st.getSchedContext? scId with
  | none => .error .objectNotFound
  | some sc =>
    if sc.boundThread != some serverTid then .error .invalidArgument
    else if !frozenOuterCallerAcceptable st serverTid originalOwner newOwner? then
      .error .invalidArgument
    -- **WS-HP HP4.7**: and the recipient, in the live order -- after the outer
    -- caller, before any write.  The head-driven trigger hands the context to the
    -- answered caller rather than to a binding's recorded owner, so this is the
    -- guard that stops a reply from overwriting a reservation that caller had
    -- acquired for itself.  A frozen surface missing a live guard is a mirror that
    -- succeeds where the kernel refuses, which `frozenRunAgrees` would report as a
    -- disagreement on exactly that state.
    else if !frozenDonationRecipientAcceptable st originalOwner then
      .error .invalidArgument
    else
      match frozenDonationHeadOf? st scId sc with
      | .error e => .error e
      | .ok head? =>
        -- **WS-RR RR8**: the record is `donationReturnSchedContext` -- the
        -- **live** function, as `donationReturnBinding` below is -- so the two
        -- surfaces cannot disagree about what a return writes into the
        -- reservation.  HP10.4's bottom-arm origin clear travels with it: this
        -- mirror did not carry that clause until FO-044 gave the frozen surface
        -- its first state with a recorded origin and the differential reported
        -- the divergence, and sharing the definition is what stops the next such
        -- clause from needing its own correction one cut later.
        let sc' := SeLe4n.Kernel.donationReturnSchedContext sc originalOwner
          (head?.bind (fun p => p.2.prev)) newOwner?
        match frozenWithObjectStored st scId.toObjId (.schedContext sc') with
        | .error e => .error e
        | .ok rebound =>
          match frozenStoreDonationHeadPop rebound scId head? with
          | .error e => .error e
          | .ok st2 =>
            -- **WS-RR RR8**: `frozenLookupTcb`, not `getTcb?`.  The live pop
            -- reads both of its TCBs with `lookupTcb`, which refuses a reserved
            -- (idle) thread id; this mirror read them with the bare accessor, so
            -- it would hand a reservation to -- or unbind -- a per-core idle
            -- thread on a state the kernel refuses with `.objectNotFound`.  A
            -- mirror that succeeds where the kernel refuses is the direction
            -- that matters on a differential surface, and the divergence was
            -- latent only because the live `.reply` path resolves its recipient
            -- from an answered caller, which is never reserved.
            match frozenLookupTcb st2 originalOwner with
            | none => .error .objectNotFound
            | some ownerTcb =>
              match frozenWithObjectStored st2 originalOwner.toObjId
                      (.tcb { ownerTcb with
                        schedContextBinding :=
                          SeLe4n.Kernel.donationReturnBinding scId newOwner? }) with
              | .error e => .error e
              | .ok st3 =>
                match frozenLookupTcb st3 serverTid with
                | none => .error .objectNotFound
                | some serverTcb =>
                  frozenWithObjectStored st3 serverTid.toObjId
                    (.tcb { serverTcb with schedContextBinding := .unbound })

/-- **WS-HP HP10.7/HP10.8, frozen mirror**: the origin may be rebound without
invalidating a live donation.

`donationOriginRebindable`'s counterpart, and it is here for the same reason it
is live: `frozenDonationRecipientAcceptable` asks that the recipient hold no
binding of its *own*, which a thread another binding names as its owner can
satisfy — and `donationOwnerValid` requires such an owner to be `.unbound` **and**
`.blockedOnReply`, so rebinding a reply-blocked thread falsifies the clause that
binding depends on.  A thread that is not reply-blocked is named by none, which is
the contrapositive this decides in O(1).

One reader differs from the live guard's, and it is immaterial: this reads
`frozenLookupTcb` (this surface's one spelling of "is this id usable") where the
live guard reads `st.getTcb?`.  The two part only on the sentinel id, and neither
resolver consults its guard on a thread it has not already resolved
(`frozenDonationOriginRecipient?` / `donationOriginRecipient?` resolve first, since
`v0.35.61`), so on every candidate the two readers see the same record. -/
def frozenDonationOriginRebindable (st : FrozenSystemState)
    (origin : SeLe4n.ThreadId) : Bool :=
  match frozenLookupTcb st origin with
  | none => true
  | some tcb =>
    match tcb.ipcState with
    | .blockedOnReply _ _ => false
    | _ => true

/-- **WS-HP HP10.8, frozen mirror**: the reservation's recorded origin, where the
pop is at the bottom of its stack and that thread passes both guards.

`donationOriginRecipient?`'s counterpart.  The frozen store holds the **live**
`SchedContext` record, so `donationOrigin` is already there and there is no field
to add — which is why this row is a resolver and a call site rather than a schema
change.  Both guards are applied to the **candidate**, so a stale origin falls
back to the reachability answer rather than refusing the pop — and, as live since
`v0.35.61`, a candidate is first of all a thread that **resolves**
(`frozenLookupTcb`): both guards pass a thread with no TCB, so without the check a
recorded origin naming none would reach the pop's own lookup as `.objectNotFound`,
a refusal on the one shape this resolver exists to make a fallback. -/
def frozenDonationOriginRecipient? (st : FrozenSystemState)
    (scId : SeLe4n.SchedContextId) : Option SeLe4n.ThreadId :=
  match frozenReplyStackOuterCaller? st scId with
  | .ok none =>
    match (st.getSchedContext? scId).bind (·.donationOrigin) with
    | none => none
    | some origin =>
      match frozenLookupTcb st origin with
      | none => none
      | some _ =>
        if frozenDonationRecipientAcceptable st origin
            && frozenDonationOriginRebindable st origin then
          some origin
        else none
  | _ => none

/-- **WS-HP HP10.8, frozen mirror**: which thread a reply's pop hands the
reservation to.

`replyDonationRecipient`'s counterpart.  The live arm flipped at HP10.7, and a
window in which the live arm redirects and this one does not is a window in which
`frozenBranchOperationChecked .endpointReplyToBlockedCaller = true` is an
over-claim — the two programs would disagree on precisely the states WS-HP HP10
exists for, under a machine-checked claim that they are run beside each other.
That is HP4.7's situation verbatim and it gets HP4.7's answer.

It is the identity wherever the resolver is silent
(`frozenReplyDonationRecipient_eq_of_no_origin`), which is every frozen state this
surface reached before the origin field carried anything. -/
def frozenReplyDonationRecipient (st : FrozenSystemState)
    (scId : SeLe4n.SchedContextId) (answeredCaller : SeLe4n.ThreadId) :
    SeLe4n.ThreadId :=
  (frozenDonationOriginRecipient? st scId).getD answeredCaller

/-- WS-HP HP10.8: the identity wherever no origin is recorded or usable. -/
@[simp] theorem frozenReplyDonationRecipient_eq_of_no_origin (st : FrozenSystemState)
    (scId : SeLe4n.SchedContextId) (answeredCaller : SeLe4n.ThreadId)
    (h : frozenDonationOriginRecipient? st scId = none) :
    frozenReplyDonationRecipient st scId answeredCaller = answeredCaller := by
  unfold frozenReplyDonationRecipient; rw [h]; rfl

/-- WS-HP HP10.8: and the recorded origin where there is one. -/
@[simp] theorem frozenReplyDonationRecipient_eq_origin (st : FrozenSystemState)
    {scId : SeLe4n.SchedContextId} {answeredCaller o : SeLe4n.ThreadId}
    (h : frozenDonationOriginRecipient? st scId = some o) :
    frozenReplyDonationRecipient st scId answeredCaller = o := by
  unfold frozenReplyDonationRecipient; rw [h]; rfl

/-- **WS-RM, frozen mirror**: the return with its outer caller resolved.

`returnDonatedSchedContextResolved`'s counterpart: the thread the context is owed
to next is read off the stack rather than supplied, so a caller cannot name one
the structure does not agree with. -/
def frozenReturnDonatedSchedContextResolved (st : FrozenSystemState)
    (serverTid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId) : Except KernelError FrozenSystemState :=
  match frozenReplyStackOuterCaller? st scId with
  | .error e => .error e
  | .ok newOwner? =>
    frozenReturnDonatedSchedContext st serverTid scId originalOwner newOwner?

/-- Q7-B: Store a TCB's IPC state in frozen state. -/
def frozenStoreTcbIpcState (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) : Except KernelError FrozenSystemState :=
  match frozenLookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match frozenStoreTcb tid { tcb with ipcState := ipcState } st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- Store a TCB's IPC state and pending message together in frozen state --
the frozen twin of the live `storeTcbIpcStateAndMessage`.  Added when the
live idle-notification block began clearing `pendingMessage` atomically with
the park (the `blockedThreadsPendingMessageConsistent` fix) and the frozen
mirror, still storing state alone, silently kept the stale message -- a
live/frozen divergence on the mirror's own content channel (PR #886
review). -/
def frozenStoreTcbIpcStateAndMessage (st : FrozenSystemState)
    (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (msg? : Option IpcMessage) : Except KernelError FrozenSystemState :=
  match frozenLookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match frozenStoreTcb tid
          { tcb with ipcState := ipcState, pendingMessage := msg? } st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

-- ============================================================================
-- Q7-A: Frozen Scheduler Helpers
-- ============================================================================

/-- R1-E/M-10: Save outgoing thread's register context to its TCB in frozen state.
Returns explicit error if the current thread's object is missing or not a TCB.
Mirrors `saveOutgoingContext` from builder phase. -/
def frozenSaveOutgoingContext (st : FrozenSystemState)
    : Except KernelError FrozenSystemState :=
  match (st.scheduler.current) with
  | none => .ok st
  | some outTid =>
      match st.getTcb? outTid with
      | some outTcb =>
          let obj := FrozenKernelObject.tcb { outTcb with registerContext := st.machine.regs }
          frozenWithObjectStored st outTid.toObjId obj
      | _ => .error .objectNotFound

/-- R1-E/M-11: Restore incoming thread's register context from its TCB in frozen state.
Returns explicit error if the thread's object is missing or not a TCB.
Mirrors `restoreIncomingContext` from builder phase. -/
def frozenRestoreIncomingContext (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    : Except KernelError FrozenSystemState :=
  match st.getTcb? tid with
  | some tcb =>
      .ok { st with machine := st.machine.setRegsOnCore bootCoreId tcb.registerContext }
  | _ => .error .objectNotFound

/-- Q7-A: Set the current thread in frozen scheduler state. -/
def frozenSetCurrentThread (tid : Option SeLe4n.ThreadId)
    (st : FrozenSystemState) : Except KernelError (Unit × FrozenSystemState) :=
  .ok ((), { st with scheduler := { st.scheduler with current := tid } })

-- ============================================================================
-- T1-A: Frozen Queue Push Tail (M-FRZ-1/2/3)
-- ============================================================================

/-- T1-A: Internal helper — compute the updated objects map for queue push tail.
Returns only the modified `FrozenMap`, not the full state. This separation
makes preservation proofs trivial: the caller wraps in `{ st with objects }`.

AE2-D (U-31): Two-phase design — validate all object keys exist BEFORE
performing any writes, preventing partial mutation on intermediate failure. -/
def frozenQueuePushTailObjects (st : FrozenSystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB)
    : Except KernelError FrozenSystemState :=
  let q := if isReceiveQ then ep.receiveQ else ep.sendQ
  match q.tail with
  | none =>
      -- AE2-D Phase 1: Validate all target keys exist before any mutation
      if !(st.objects.contains endpointId && st.objects.contains tid.toObjId) then
        .error .objectNotFound
      else
      -- AE2-D Phase 2: Apply writes (guaranteed to succeed by Phase 1)
      let q' : IntrusiveQueue := { head := some tid, tail := some tid }
      let ep' : Endpoint := if isReceiveQ
        then { ep with receiveQ := q' }
        else { ep with sendQ := q' }
      let tcb' := { tcb with
        queuePrev := none
        queuePPrev := some .endpointHead
        queueNext := none }
      -- Both writes are guaranteed by Phase 1; the refusals are unreachable.
      match frozenWithObjectStored st endpointId (.endpoint ep') with
      | .ok st1 => frozenWithObjectStored st1 tid.toObjId (.tcb tcb')
      | .error e => .error e
  | some tailTid =>
      match st.getTcb? tailTid with
      | some tailTcb =>
          -- AE2-D Phase 1: Validate all target keys exist before any mutation
          if !(st.objects.contains endpointId && st.objects.contains tailTid.toObjId
               && st.objects.contains tid.toObjId) then
            .error .objectNotFound
          else
          -- AE2-D Phase 2: Apply writes (guaranteed to succeed by Phase 1)
          let q' : IntrusiveQueue := { head := q.head, tail := some tid }
          let ep' : Endpoint := if isReceiveQ
            then { ep with receiveQ := q' }
            else { ep with sendQ := q' }
          let tailTcb' := { tailTcb with queueNext := some tid }
          let tcb' := { tcb with
            queuePrev := some tailTid
            queuePPrev := some (.tcbNext tailTid)
            queueNext := none }
          -- All three writes are guaranteed by Phase 1.
          match frozenWithObjectStored st endpointId (.endpoint ep') with
          | .ok st1 =>
              match frozenWithObjectStored st1 tailTid.toObjId (.tcb tailTcb') with
              | .ok st2 => frozenWithObjectStored st2 tid.toObjId (.tcb tcb')
              | .error e => .error e
          | .error e => .error e
      | _ => .error .objectNotFound

/-- The enqueue's writes are frozen stores, so it inherits their frame.

The leaf closer **searches** for the store chain rather than naming its shape:
`solve_by_elim` composes `frozenOnlyObjects_trans` over whichever
`frozenWithObjectStored ... = .ok _` hypotheses the branch left in context.  A
store added to either arm therefore costs this proof nothing, where the
superseded proof destructured the body down to `FrozenMap.set` and closed each
leaf by `injection` on a literal `{ st with objects := _ }` -- coupling it to
how many branches the body had and to every write being spelled inline. -/
theorem frozenQueuePushTailObjects_only_modifies_objects
    {st st' : FrozenSystemState} {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {ep : Endpoint} {tcb : TCB}
    (hOk : frozenQueuePushTailObjects st endpointId isReceiveQ tid ep tcb = .ok st') :
    ∃ objects', st' = { st with objects := objects' } := by
  simp only [frozenQueuePushTailObjects] at hOk
  repeat' split at hOk
  -- Unwind whatever store chain the branch left in context, rather than naming
  -- its length: each step peels one `frozenWithObjectStored ... = .ok stK`
  -- hypothesis off the front and the walk stops at `frozenOnlyObjects_rfl` when
  -- it reaches `st` itself.  Spelled inline rather than behind a tactic `macro`,
  -- because declaration-minting machinery is invisible to this tree's text
  -- censuses and one call site buys no sharing to pay for that.
  all_goals first
    | (simp at hOk; done)
    | (repeat first
        | exact frozenOnlyObjects_rfl
        | refine frozenOnlyObjects_trans ?_
            (frozenWithObjectStored_only_modifies_objects (by assumption)))

def frozenQueuePushTail (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st : FrozenSystemState)
    : Except KernelError FrozenSystemState :=
  match st.getObject? endpointId with
  | some (.endpoint ep) =>
      match frozenLookupTcb st tid with
      | none => .error .objectNotFound
      | some tcb =>
          -- Dual-queue invariant: reject if thread already has queue links (T1-A)
          if tcb.queuePPrev.isSome || tcb.queuePrev.isSome || tcb.queueNext.isSome then
            .error .illegalState
          else
          frozenQueuePushTailObjects st endpointId isReceiveQ tid ep tcb
  | some _ => .error .invalidCapability
  | none => .error .objectNotFound

/-- **WS-SM SM6.B (PR #873 round 8): unlink a thread from an endpoint queue.**

The frozen counterpart of `endpointQueueRemoveDual`, and it did not exist — which
is why `frozenNotificationSignal` had no bound-delivery branch to fall into and
stored the badge on the notification instead, leaving the bound TCB blocked and
recording the signaller's provenance on the wrong object.

O(1) rather than a walk, because the model maintains `queuePrev`
(`frozenQueuePushTailObjects` sets it on every push): the node's own neighbours
are named by its links, so removal is head/tail fix-up plus at most two relinks.
A thread with no `queuePPrev` is on no queue at all and is refused
(`.illegalState`) rather than silently "removed" — the same guard
`frozenQueuePushTail` applies in the opposite direction. -/
def frozenQueueRemove (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st : FrozenSystemState)
    : Except KernelError FrozenSystemState :=
  match st.getObject? endpointId with
  | some (.endpoint ep) =>
      match frozenLookupTcb st tid with
      | none => .error .objectNotFound
      | some tcb =>
        match tcb.queuePPrev with
        -- `v0.35.59`: `.endpointQueueEmpty`, which is what
        -- `endpointQueueRemoveDual` answers here.  This arm said `.illegalState`,
        -- and `frozenRunAgrees` compares error codes — so the two disagreed on a
        -- state either side could be driven to, and nothing drove them there.
        | none => .error .endpointQueueEmpty
        | some pprev =>
          let q := if isReceiveQ then ep.receiveQ else ep.sendQ
          -- `v0.35.59`: the live removal's whole store-free precondition, by
          -- calling the definition the live removal calls.
          --
          -- `endpointQueueRemoveDual` refuses four things before it writes
          -- anything: a `queuePPrev` of `none` (above), a queue missing either
          -- boundary, a back-pointer that does not pair with `queuePrev` or
          -- disagrees with where the thread sits in the queue (WS-RR RR8.3), and
          -- a queue `tail` field disagreeing with the removed thread's
          -- `queueNext` (RR8.4).  This mirror refused only the first, and with the
          -- wrong code — so on a state violating any of the others it
          -- **succeeded where the kernel refuses**, which is the direction that
          -- matters on a differential surface: `frozenRunAgrees` compares
          -- outcomes, so a mirror more permissive than its subject reports
          -- agreement on states the kernel never reaches and says nothing at all
          -- about the states that distinguish them.
          --
          -- RR8.4 registered that rather than closing it, `dualQueueRemovalGuard`
          -- then living in the IPC layer this surface deliberately does not
          -- import.  `v0.35.59` moved the guard to the model beside the records it
          -- reads and named the *whole* condition `dualQueueRemovalEnabled`, so
          -- both removals read one definition and a condition added to it reaches
          -- both by construction.  Carrying the named guard alone would have left
          -- the unnamed boundary check behind — a subset of the refusal set,
          -- reached through a shared name, which reads like agreement.
          if !dualQueueRemovalEnabled q tid tcb pprev then .error .illegalState
          else
          -- **WS-RR RR8.4**: `queueRemoveBoundary` (`Model/Object/Types.lean`),
          -- the one definition of what a removal writes to a queue's boundaries,
          -- shared with all three live removals.  This was the **fifth** asker of
          -- that question and the one the sweep nearly missed, which is the
          -- position this surface kept occupying: until `v0.35.60` it was reached
          -- by neither library root, and it holds the **live** `TCB`, so a
          -- model-level definition applies to it directly and a sweep that stopped
          -- at the kernel tree left it behind.  It is in `SeLe4n.lean` now, so a
          -- root-derived sweep reaches it.
          --
          -- It already asked the **fact** (`q.tail == some tid`) rather than the
          -- proxy (`queueNext = none`) the live dual removal used, so the mirror
          -- was right on the tail question where the operation it mirrors was
          -- wrong — and nothing compared them on the state where they part.  The
          -- boundary written here is unchanged; `==` and the propositional `if`
          -- agree on `Option ThreadId` by `LawfulBEq`.
          let q' : IntrusiveQueue := queueRemoveBoundary q tid tcb
          let ep' : Endpoint := if isReceiveQ
            then { ep with receiveQ := q' }
            else { ep with sendQ := q' }
          let tcb' := { tcb with queuePrev := none, queueNext := none, queuePPrev := none }
          match frozenWithObjectStored st endpointId (.endpoint ep') with
          | .error e => .error e
          | .ok st1 =>
            match frozenWithObjectStored st1 tid.toObjId (.tcb tcb') with
            | .error e => .error e
            | .ok st2 =>
              -- Predecessor now points past the removed node.
              --
              -- `v0.35.59`: and it must *be* the predecessor.
              -- `endpointQueueRemoveDual` refuses `.illegalState` when the
              -- resolved predecessor's own `queueNext` does not name `tid`; this
              -- patched it unconditionally, so a one-sided link was repaired here
              -- and refused there.  The check is
              -- `queuePredecessorNamesSuccessor`, the definition the live removal
              -- reads, and it needs a store lookup, which is why each side
              -- resolves `prevTcb` itself rather than sharing one call.  The
              -- result is an `Except` rather than an `Option` because the two
              -- failures are different: an unresolvable predecessor is
              -- `.objectNotFound` and a non-reciprocating one is `.illegalState`.
              let afterPrev : Except KernelError FrozenSystemState :=
                match tcb.queuePrev with
                | none => .ok st2
                | some prevTid =>
                  match st2.getTcb? prevTid with
                  | some prevTcb =>
                      if !queuePredecessorNamesSuccessor prevTcb tid then .error .illegalState
                      else
                        frozenWithObjectStored st2 prevTid.toObjId
                          (.tcb { prevTcb with queueNext := tcb.queueNext })
                  | _ => .error .objectNotFound
              match afterPrev with
              | .error e => .error e
              | .ok st3 =>
                -- Successor's back-links move to the removed node's predecessor.
                match tcb.queueNext with
                | none => .ok st3
                | some nextTid =>
                  match st3.getTcb? nextTid with
                  | some nextTcb =>
                      frozenWithObjectStored st3 nextTid.toObjId (.tcb { nextTcb with
                        queuePrev := tcb.queuePrev,
                        queuePPrev := match tcb.queuePrev with
                          | none => some .endpointHead
                          | some prevTid => some (.tcbNext prevTid) })
                  | _ => .error .objectNotFound
  | some _ => .error .invalidCapability
  | none => .error .objectNotFound

/-- T1-E: Key structural lemma: `frozenQueuePushTail` only modifies `objects`.
Every success path returns `{ st with objects := _ }`. -/
theorem frozenQueuePushTail_only_modifies_objects
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : FrozenSystemState)
    (hOk : frozenQueuePushTail endpointId isReceiveQ tid st = .ok st') :
    ∃ objects', st' = { st with objects := objects' } := by
  simp only [frozenQueuePushTail, frozenLookupTcb] at hOk
  -- The lookups and the queue-link precondition write nothing; the one arm that
  -- reaches a write delegates to the enqueue, which carries the frame.
  repeat' split at hOk
  all_goals first
    | (simp at hOk; done)
    | exact frozenQueuePushTailObjects_only_modifies_objects hOk

-- ============================================================================
-- Q7-A: Core Theorems
-- ============================================================================

/-- Q7-A: `frozenLookupObject` does not modify frozen state. -/
theorem frozenLookupObject_state_unchanged
    (id : SeLe4n.ObjId) (st : FrozenSystemState)
    (obj : FrozenKernelObject) (st' : FrozenSystemState)
    (hOk : frozenLookupObject id st = .ok (obj, st')) :
    st' = st := by
  unfold frozenLookupObject at hOk
  split at hOk <;> simp at hOk
  exact hOk.2.symm

/-- Q7-A: `frozenStoreObject` only modifies the objects field. -/
theorem frozenStoreObject_preserves_scheduler
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st : FrozenSystemState) (st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  -- The frame is the write's, stated once at `frozenWithObjectStored`.
  obtain ⟨_, _, hSt⟩ := frozenStoreObject_ok hOk
  rw [hSt]

/-- Q7-A: `frozenStoreObject` preserves the machine state. -/
theorem frozenStoreObject_preserves_machine
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st : FrozenSystemState) (st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.machine = st.machine := by
  -- The frame is the write's, stated once at `frozenWithObjectStored`.
  obtain ⟨_, _, hSt⟩ := frozenStoreObject_ok hOk
  rw [hSt]

end SeLe4n.Kernel.FrozenOps
