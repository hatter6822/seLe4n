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

**STATUS: Experimental — post-1.0 hardening candidate, registered in the *Registered debt index* (table C.1) in `docs/REGISTERED_DEBT.md`,
row 14. Not in production import chain.**

AG8-D production decision (H3-PROOF-05): FrozenOps evaluated for H3 promotion.
Decision: **defer as post-1.0 hardening candidate**. Rationale:
1. All 24 per-subsystem operations have preservation theorems (33 total).
2. `FrozenSchedulerState.replenishQueue` present (AG1-E).
3. `FrozenMap` commutativity proofs complete.
4. However, the two-phase architecture requires RPi5 performance benchmarking
   to validate that the freeze→operate→thaw cycle does not exceed the WCRT
   budget on Cortex-A76. This cannot be assessed until a post-1.0 hardware-
   testing workstream is opened.
5. Zero production consumers — promoting now would add import weight without
   a runtime benefit.

These modules implement the frozen-state kernel monad for a future
architecture where syscall processing operates on immutable
`FrozenSystemState` snapshots. Currently exercised by test suites only.
Integration into the production API layer is a post-1.0 hardening candidate
(registered in `docs/REGISTERED_DEBT.md`, Registered debt index, C.1)
pending RPi5 benchmark data.
(AE2-E / U-02 / AG8-D)

**Subsystem status (W3-G):** FrozenOps has zero production consumers — the
kernel API (`API.lean`) does not reference it. Only `FrozenOpsSuite.lean` and
`TwoPhaseArchSuite.lean` import it. This subsystem is retained as **architectural
validation infrastructure** for the two-phase (builder→frozen) state model:

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

/-- Q7-B: Store a frozen kernel object at an existing key.
Uses `FrozenMap.set` — in-place array update. Returns error if key is
not in the frozen map (key was not present at freeze time). -/
def frozenStoreObject (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    : FrozenKernel Unit :=
  fun st =>
    match st.objects.set id obj with
    | some objects' => .ok ((), { st with objects := objects' })
    | none => .error .objectNotFound

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
          { st with objects := st.objects.insert tid.toObjId (.tcb tcb') }
        -- **Queued ANYWHERE, not queued at `oldPrio`.**  The live
        -- `updatePipBoost` asks `tid ∈ runQueueOnCore` -- membership in the
        -- queue -- and then `RunQueue.remove tid` takes it out of whichever
        -- bucket holds it.  Looking only in the bucket `oldPrio` names assumes
        -- a thread's bucket always equals its effective priority, and a state
        -- where the two have drifted apart is exactly the one a reversion has
        -- to repair: on such a state the thread was left where it was while the
        -- live kernel moved it, which the operation-level differential (FO-041)
        -- caught on its first run.  `frozenRemoveRunnable` searches every
        -- bucket for the same reason, and says so.
        let queued := st'.scheduler.byPriority.indexMap.toList.any (fun kv =>
          ((st'.scheduler.byPriority.get? kv.1).getD []).contains tid)
        if oldPrio == newPrio || !queued then st'
        else
          let dropped := st'.scheduler.byPriority.indexMap.toList.foldl
            (fun bp kv =>
              let bucket := (bp.get? kv.1).getD []
              if bucket.contains tid then bp.insert kv.1 (bucket.filter (· != tid)) else bp)
            st'.scheduler.byPriority
          let newBucket := (dropped.get? newPrio).getD []
          { st' with scheduler := { st'.scheduler with
              byPriority := dropped.insert newPrio (newBucket ++ [tid]) } }

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
        match st.objects.set rid.toObjId (.reply { r with caller := some caller }) with
        | none => .error .objectNotFound
        | some objects' =>
            let st1 : FrozenSystemState := { st with objects := objects' }
            match frozenLookupTcb st1 caller with
            | none => .error .objectNotFound
            | some tcb =>
                if tcb.replyObject.isNone then
                  match st1.objects.set caller.toObjId
                      (.tcb { tcb with replyObject := some rid }) with
                  | none => .error .objectNotFound
                  | some objects'' => .ok { st1 with objects := objects'' }
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
    match st.objects.set above.toObjId (.reply { a with prev := none }) with
    | none => .error .objectNotFound
    | some objects' => .ok { st with objects := objects' }
  | some (below, b) =>
    match st.objects.set above.toObjId (.reply { a with prev := some below }) with
    | none => .error .objectNotFound
    | some o1 =>
      match o1.set below.toObjId (.reply { b with next := some (.frame above) }) with
      | none => .error .objectNotFound
      | some o2 =>
        match o2.set rid.toObjId (.reply { r with prev := none }) with
        | none => .error .objectNotFound
        | some o3 => .ok { st with objects := o3 }

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
      (match st.objects.set above.toObjId (.reply { a with prev := none }) with
       | none => .error .objectNotFound
       | some objects' => .ok { st with objects := objects' }) := by
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
      match st.objects.set rid.toObjId (.reply { h with prev := none, next := none }) with
      | none => .error .objectNotFound
      | some cleared =>
        let st1 : FrozenSystemState := { st with objects := cleared }
        match r.prev with
        | none => .ok st1
        | some below =>
          match st1.getReply? below with
          | none => .error .objectNotFound
          | some b =>
            match st1.objects.set below.toObjId
                    (.reply { b with next := some (.head scId) }) with
            | none => .error .objectNotFound
            | some reheaded => .ok { st1 with objects := reheaded }

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
        let sc' := { sc with boundThread := some originalOwner,
                             scReply := head?.bind (fun p => p.2.prev) }
        match st.objects.set scId.toObjId (.schedContext sc') with
        | none => .error .objectNotFound
        | some rebound =>
          match frozenStoreDonationHeadPop { st with objects := rebound } scId head? with
          | .error e => .error e
          | .ok st2 =>
            match st2.getTcb? originalOwner with
            | none => .error .objectNotFound
            | some ownerTcb =>
              match st2.objects.set originalOwner.toObjId
                      (.tcb { ownerTcb with
                        schedContextBinding :=
                          SeLe4n.Kernel.donationReturnBinding scId newOwner? }) with
              | none => .error .objectNotFound
              | some owned =>
                let st3 : FrozenSystemState := { st2 with objects := owned }
                match st3.getTcb? serverTid with
                | none => .error .objectNotFound
                | some serverTcb =>
                  match st3.objects.set serverTid.toObjId
                          (.tcb { serverTcb with
                            schedContextBinding := .unbound }) with
                  | none => .error .objectNotFound
                  | some released => .ok { st3 with objects := released }

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
          match st.objects.set outTid.toObjId obj with
          | some objects' => .ok { st with objects := objects' }
          | none => .error .objectNotFound
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
def frozenQueuePushTailObjects (objects : FrozenMap SeLe4n.ObjId FrozenKernelObject)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB)
    : Except KernelError (FrozenMap SeLe4n.ObjId FrozenKernelObject) :=
  let q := if isReceiveQ then ep.receiveQ else ep.sendQ
  match q.tail with
  | none =>
      -- AE2-D Phase 1: Validate all target keys exist before any mutation
      if !(objects.contains endpointId && objects.contains tid.toObjId) then
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
      match objects.set endpointId (.endpoint ep') with
      | some objects1 =>
          match objects1.set tid.toObjId (.tcb tcb') with
          | some objects2 => .ok objects2
          | none => .error .objectNotFound  -- unreachable after Phase 1
      | none => .error .objectNotFound  -- unreachable after Phase 1
  | some tailTid =>
      match objects.get? tailTid.toObjId with
      | some (.tcb tailTcb) =>
          -- AE2-D Phase 1: Validate all target keys exist before any mutation
          if !(objects.contains endpointId && objects.contains tailTid.toObjId
               && objects.contains tid.toObjId) then
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
          match objects.set endpointId (.endpoint ep') with
          | some objects1 =>
              match objects1.set tailTid.toObjId (.tcb tailTcb') with
              | some objects2 =>
                  match objects2.set tid.toObjId (.tcb tcb') with
                  | some objects3 => .ok objects3
                  | none => .error .objectNotFound  -- unreachable after Phase 1
              | none => .error .objectNotFound  -- unreachable after Phase 1
          | none => .error .objectNotFound  -- unreachable after Phase 1
      | _ => .error .objectNotFound

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
          match frozenQueuePushTailObjects st.objects endpointId isReceiveQ tid ep tcb with
          | .ok objects' => .ok { st with objects := objects' }
          | .error e => .error e
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
        if tcb.queuePPrev.isNone then .error .illegalState
        else
          let q := if isReceiveQ then ep.receiveQ else ep.sendQ
          let q' : IntrusiveQueue :=
            { head := if q.head == some tid then tcb.queueNext else q.head,
              tail := if q.tail == some tid then tcb.queuePrev else q.tail }
          let ep' : Endpoint := if isReceiveQ
            then { ep with receiveQ := q' }
            else { ep with sendQ := q' }
          let tcb' := { tcb with queuePrev := none, queueNext := none, queuePPrev := none }
          match st.objects.set endpointId (.endpoint ep') with
          | none => .error .objectNotFound
          | some o1 =>
            match o1.set tid.toObjId (.tcb tcb') with
            | none => .error .objectNotFound
            | some o2 =>
              -- Predecessor now points past the removed node.
              let afterPrev : Option (FrozenMap SeLe4n.ObjId FrozenKernelObject) :=
                match tcb.queuePrev with
                | none => some o2
                | some prevTid =>
                  match o2.get? prevTid.toObjId with
                  | some (.tcb prevTcb) =>
                      o2.set prevTid.toObjId (.tcb { prevTcb with queueNext := tcb.queueNext })
                  | _ => none
              match afterPrev with
              | none => .error .objectNotFound
              | some o3 =>
                -- Successor's back-links move to the removed node's predecessor.
                match tcb.queueNext with
                | none => .ok { st with objects := o3 }
                | some nextTid =>
                  match o3.get? nextTid.toObjId with
                  | some (.tcb nextTcb) =>
                      match o3.set nextTid.toObjId (.tcb { nextTcb with
                          queuePrev := tcb.queuePrev,
                          queuePPrev := match tcb.queuePrev with
                            | none => some .endpointHead
                            | some prevTid => some (.tcbNext prevTid) }) with
                      | some o4 => .ok { st with objects := o4 }
                      | none => .error .objectNotFound
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
  -- Split all nested matches including the queue-link precondition `if`
  repeat split at hOk
  all_goals (repeat split at hOk)
  all_goals (repeat split at hOk)
  -- Close goals: error paths close by simp (derives False), success paths by injection
  all_goals (first | (simp at hOk; done) | (injection hOk with hEq; exact ⟨_, hEq.symm⟩))

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
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' => simp [hSet] at hOk; rw [← hOk]
  | none => simp [hSet] at hOk

/-- Q7-A: `frozenStoreObject` preserves the machine state. -/
theorem frozenStoreObject_preserves_machine
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st : FrozenSystemState) (st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' => simp [hSet] at hOk; rw [← hOk]
  | none => simp [hSet] at hOk

end SeLe4n.Kernel.FrozenOps
