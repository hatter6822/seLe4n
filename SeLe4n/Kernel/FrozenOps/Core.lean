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

**STATUS: Experimental — post-1.0 hardening candidate, registered in the *Registered debt index* (table C.1) in `docs/WORKSTREAM_HISTORY.md`,
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
(registered in `docs/WORKSTREAM_HISTORY.md`, Registered debt index, C.1)
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
    match st.objects.get? id with
    | some obj => .ok (obj, st)
    | none => .error .objectNotFound

/-- Q7-A: Look up a TCB by ThreadId in frozen state.
Mirrors `lookupTcb` from builder phase: sentinel check + type match. -/
def frozenLookupTcb (st : FrozenSystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  if tid.isReserved then none
  else match st.objects.get? tid.toObjId with
  | some (.tcb tcb) => some tcb
  | _ => none

/-- Q7-A: Look up an endpoint by ObjId in frozen state. -/
def frozenLookupEndpoint (st : FrozenSystemState) (epId : SeLe4n.ObjId) : Option Endpoint :=
  match st.objects.get? epId with
  | some (.endpoint ep) => some ep
  | _ => none

/-- Q7-A: Look up a notification by ObjId in frozen state. -/
def frozenLookupNotification (st : FrozenSystemState) (nId : SeLe4n.ObjId) : Option Notification :=
  match st.objects.get? nId with
  | some (.notification n) => some n
  | _ => none

/-- Q7-A: Look up a frozen CNode by ObjId in frozen state. -/
def frozenLookupCNode (st : FrozenSystemState) (cnId : SeLe4n.ObjId) : Option FrozenCNode :=
  match st.objects.get? cnId with
  | some (.cnode cn) => some cn
  | _ => none

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
      let prio : SeLe4n.Priority :=
        match tcb.pipBoost with
        | none => tcb.priority
        | some boost => ⟨Nat.max tcb.priority.val boost.val⟩
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
  match st.objects.get? rid.toObjId with
  | some (.reply r) =>
      if r.caller.isNone then
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
      match st.objects.get? outTid.toObjId with
      | some (.tcb outTcb) =>
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
  match st.objects.get? tid.toObjId with
  | some (.tcb tcb) =>
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
  match st.objects.get? endpointId with
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
  match st.objects.get? endpointId with
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
