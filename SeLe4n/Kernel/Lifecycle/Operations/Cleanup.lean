/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.IPC.Operations
import SeLe4n.Kernel.Service.Registry

/-!
AN4-G.5 (LIF-M05) child module extracted from
`SeLe4n.Kernel.Lifecycle.Operations`. Contains the cleanup-primitive
defs (`lifecycleRetypeAuthority`, `removeThreadFromQueue`,
`spliceOutMidQueueNode`, `removeFromAllEndpointQueues`,
`removeFromAllNotificationWaitLists`, `cleanupDonatedSchedContext`,
`cleanupTcbReferences`) that form the building blocks of the retype
cleanup pipeline. All declarations retain their original names, order,
and proofs. Private helpers are promoted to file-boundary scope so the
sibling `CleanupPreservation` module can reference them without
re-proving.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Lifecycle authority required to retype an object identity in this slice.

U-H14: The authority capability must target the object directly and include
`retype` rights. This matches the API dispatch mapping (`.lifecycleRetype => .retype`
in `requiredRight`). Previously checked `.write`, creating a mismatch where
callers with `.retype` but not `.write` were incorrectly rejected. -/
def lifecycleRetypeAuthority (cap : Capability) (target : SeLe4n.ObjId) : Bool :=
  decide (cap.target = .object target) && Capability.hasRight cap .retype


-- ============================================================================
-- WS-H2: Lifecycle Safety Guards
-- ============================================================================

/-- R4-A.1: Remove a ThreadId from an intrusive queue's head/tail pointers.
    If the head points to `tid`, advances to the TCB's `queueNext` successor
    (preserving queue accessibility for remaining threads). If `tid` is the
    tail, retreats to the TCB's `queuePrev` predecessor.

    **W6-A (M-7): TCB existence invariant.** The `none` branch of `lookupTcb`
    should never be taken during normal cleanup: `lifecyclePreRetypeCleanup`
    calls `cleanupTcbReferences` *before* the TCB is retyped, so the TCB
    is still present in `st.objects`. The `(none, none)` fallback is
    defensive-safe — it clears both head and tail pointers for this endpoint
    when `tid` matches, which is sound (no dangling pointers remain) but
    loses queue structure. If this branch is reached, it indicates a
    programming error in the cleanup call order, not a data corruption risk.
    The `tcbQueueChainAcyclic` invariant (from `dualQueueSystemInvariant`)
    guarantees that queued threads have valid TCB entries.

    **AN4-G.1 (LIF-M01)**: The fallback is formally characterised by
    `removeThreadFromQueue_tcb_present` below — callers that can witness a
    TCB at `tid` obtain the principled queue-advance semantics, and the
    branch's exit-when-TCB-is-absent behaviour is clamped to the
    no-dangling-pointers invariant (`head` and `tail` both cleared if either
    pointed at `tid`). The absurdity of the branch under real cleanup call
    chains is recorded as a fact consumers can derive; a full
    signature-tightening (wrapping the function in `Except` with a
    `.ipcInvariantViolated` error for the absent case) is tracked for AN6
    cross-subsystem composition once `dualQueueSystemInvariant` is threaded
    through every caller. -/
def removeThreadFromQueue (st : SystemState) (q : IntrusiveQueue) (tid : SeLe4n.ThreadId) : IntrusiveQueue :=
  let advance := match lookupTcb st tid with
    | some tcb => (tcb.queueNext, tcb.queuePrev)
    | none => (none, none)  -- defensive: see W6-A / AN4-G.1 doc above
  { head := if q.head = some tid then advance.1 else q.head,
    tail := if q.tail = some tid then advance.2 else q.tail }

/-- AN4-G.1 (LIF-M01): When `lookupTcb st tid = some tcb` (the cleanup-ordering
invariant guarantees this at every call site), `removeThreadFromQueue`
reduces to the principled "advance past `tid`" semantics: if the queue
head points at `tid`, replace with the TCB's `queueNext`; if the tail
points at `tid`, replace with `queuePrev`. The `(none, none)` defensive
fallback is therefore formally unreachable whenever the witness holds. -/
theorem removeThreadFromQueue_tcb_present
    (st : SystemState) (q : IntrusiveQueue) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : lookupTcb st tid = some tcb) :
    removeThreadFromQueue st q tid =
      { head := if q.head = some tid then tcb.queueNext else q.head,
        tail := if q.tail = some tid then tcb.queuePrev else q.tail } := by
  simp [removeThreadFromQueue, hTcb]

/-- T5-E (M-LCS-1): Splice a mid-queue node out of the intrusive doubly-linked list.
    When a TCB `tid` is deleted, its predecessor's `queueNext` must point to `tid`'s
    successor, and `tid`'s successor's `queuePrev` must point to `tid`'s predecessor.
    This patches the interior links that `removeThreadFromQueue` does not handle.

    The splice reads the removed TCB's links from the **original** state (before
    mutations) to ensure consistent predecessor/successor identification. -/
def spliceOutMidQueueNode (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match lookupTcb st tid with
  | none => st
  | some tcb =>
    -- Compute the new objects table with predecessor/successor patches.
    -- Each patch reads from the current `objs` (not original `st.objects`)
    -- so that the successor sees the predecessor's patch when prevTid == nextTid.
    let objs := st.objects
    -- Patch predecessor's queueNext to skip over tid
    let objs := match tcb.queuePrev with
      | none => objs
      | some prevTid =>
        match objs[prevTid.toObjId]? with
        | some (.tcb prevTcb) =>
          objs.insert prevTid.toObjId (.tcb { prevTcb with queueNext := tcb.queueNext })
        | _ => objs
    -- Patch successor's queuePrev to skip over tid (reads patched objs)
    let objs := match tcb.queueNext with
      | none => objs
      | some nextTid =>
        match objs[nextTid.toObjId]? with
        | some (.tcb nextTcb) =>
          objs.insert nextTid.toObjId (.tcb { nextTcb with queuePrev := tcb.queuePrev })
        | _ => objs
    { st with objects := objs }

/-- R4-A.1 (M-12) + T5-E (M-LCS-1): Remove a ThreadId from all endpoint send/receive
    queues. First splices the mid-queue node out by patching predecessor/successor
    links, then adjusts head/tail pointers in each endpoint queue.

    Iterates over all endpoint objects in `st.objects` and advances any
    head/tail references to `tid` in both `sendQ` and `receiveQ` to the
    TCB's queue successor/predecessor. TCB queue links are read from the
    original state (before any fold mutations) to ensure consistent reads.
    This prevents dangling queue references after a TCB is retyped. -/
def removeFromAllEndpointQueues (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  -- T5-E: First splice out mid-queue links, then adjust head/tail pointers
  let stSpliced := spliceOutMidQueueNode st tid
  stSpliced.objects.fold stSpliced fun acc oid obj =>
    match obj with
    | .endpoint ep =>
      let ep' : Endpoint := {
        sendQ := removeThreadFromQueue stSpliced ep.sendQ tid,
        receiveQ := removeThreadFromQueue stSpliced ep.receiveQ tid }
      { acc with objects := acc.objects.insert oid (.endpoint ep') }
    | _ => acc

/-- R4-A.2 (M-12): Remove a ThreadId from all notification waiting lists.
    Iterates over all notification objects in `st.objects` and filters out
    `tid` from each notification's `waitingThreads` list. -/
def removeFromAllNotificationWaitLists (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  st.objects.fold st fun acc oid obj =>
    match obj with
    | .notification notif =>
      let notif' : Notification := {
        notif with waitingThreads := notif.waitingThreads.filter (· != tid) }
      { acc with objects := acc.objects.insert oid (.notification notif') }
    | _ => acc

/-- Z7-P / AJ1-A (M-14): Return donated SchedContext before destroying a thread.
If the thread has `.donated` binding, return the SchedContext to the original
owner. Otherwise, return the state unchanged. Only modifies `objects`.
Returns `Except` to propagate `returnDonatedSchedContext` errors — a failed
cleanup would leave the SchedContext's `boundThread` pointing to a destroyed
TCB (dangling reference). -/
def cleanupDonatedSchedContext (st : SystemState) (tid : SeLe4n.ThreadId)
    : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .ok st
  | some tcb =>
    match tcb.schedContextBinding with
    | .donated scId originalOwner =>
      returnDonatedSchedContext st tid scId originalOwner
    | _ => .ok st

/-- Z7-P / AJ1-A (M-14): cleanupDonatedSchedContext preserves the scheduler
(conditional on success). -/
theorem cleanupDonatedSchedContext_scheduler_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (h : cleanupDonatedSchedContext st tid = .ok st') :
    st'.scheduler = st.scheduler := by
  simp only [cleanupDonatedSchedContext] at h
  split at h
  · injection h with h; subst h; rfl
  · split at h <;> first
      | (injection h with h; subst h; rfl)
      | exact returnDonatedSchedContext_scheduler_eq st st' tid _ _ h


/-- WS-H2/H-05, R4-A.3 (M-12): Clean up external references to a TCB being retyped away.
    Removes the ThreadId from:
    1. The scheduler run queue (`removeRunnable`)
    2. All endpoint send/receive queues (`removeFromAllEndpointQueues`)
    3. All notification waiting lists (`removeFromAllNotificationWaitLists`)
    Note: Donated SchedContext cleanup (`cleanupDonatedSchedContext`) is handled
    separately in `lifecyclePreRetypeCleanup` BEFORE this function is called,
    because `storeObject` modifies lifecycle metadata and `cleanupTcbReferences`
    must preserve lifecycle for its proofs.
    This prevents dangling-reference scenarios after a TCB is retyped. -/
def cleanupTcbReferences (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  let st := removeRunnable st tid
  let st := removeFromAllEndpointQueues st tid
  removeFromAllNotificationWaitLists st tid


end SeLe4n.Kernel
