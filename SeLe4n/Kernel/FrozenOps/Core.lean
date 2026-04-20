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

**STATUS: Experimental — deferred to WS-V. Not in production import chain.**

AG8-D production decision (H3-PROOF-05): FrozenOps evaluated for H3 promotion.
Decision: **defer to WS-V**. Rationale:
1. All 24 per-subsystem operations have preservation theorems (33 total).
2. `FrozenSchedulerState.replenishQueue` present (AG1-E).
3. `FrozenMap` commutativity proofs complete.
4. However, the two-phase architecture requires RPi5 performance benchmarking
   to validate that the freeze→operate→thaw cycle does not exceed the WCRT
   budget on Cortex-A76. This cannot be assessed until WS-V hardware testing.
5. Zero production consumers — promoting now would add import weight without
   a runtime benefit.

These modules implement the frozen-state kernel monad for a future
architecture where syscall processing operates on immutable
`FrozenSystemState` snapshots. Currently exercised by test suites only.
Integration into the production API layer is planned for WS-V
when the performance characteristics of the two-phase approach can be
benchmarked on RPi5. (AE2-E / U-02 / AG8-D)

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
All lookups use `FrozenMap.get?` (index lookup + array access) and all
mutations use `FrozenMap.set` (in-place array update at existing index).

The index map is never modified after freeze — it is immutable. All
`Fin` accesses are within bounds by construction. No fuel or dynamic
resizing is needed.

## Design

- `FrozenKernel α`: state monad over `FrozenSystemState` with `KernelError`
- `frozenLookupObject`: typed object lookup via `FrozenMap.get?`
- `frozenStoreObject`: value-only mutation via `FrozenMap.set`
- `frozenLookupTcb`: typed TCB extraction with sentinel check
- `frozenStoreTcb`: convenience wrapper for TCB updates
-/

namespace SeLe4n.Kernel.FrozenOps

open SeLe4n.Model
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

/-- Q7-B: Store a TCB's IPC state in frozen state. -/
def frozenStoreTcbIpcState (st : FrozenSystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) : Except KernelError FrozenSystemState :=
  match frozenLookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match frozenStoreTcb tid { tcb with ipcState := ipcState } st with
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
  match st.scheduler.current with
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
      .ok { st with machine := { st.machine with regs := tcb.registerContext } }
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
