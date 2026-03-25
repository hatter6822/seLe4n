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
    tail, retreats to the TCB's `queuePrev` predecessor. Falls back to `none`
    if the TCB cannot be looked up (defensive — the TCB should still exist at
    cleanup time since cleanup runs before retype). -/
private def removeThreadFromQueue (st : SystemState) (q : IntrusiveQueue) (tid : SeLe4n.ThreadId) : IntrusiveQueue :=
  let advance := match lookupTcb st tid with
    | some tcb => (tcb.queueNext, tcb.queuePrev)
    | none => (none, none)
  { head := if q.head = some tid then advance.1 else q.head,
    tail := if q.tail = some tid then advance.2 else q.tail }

/-- T5-E (M-LCS-1): Splice a mid-queue node out of the intrusive doubly-linked list.
    When a TCB `tid` is deleted, its predecessor's `queueNext` must point to `tid`'s
    successor, and `tid`'s successor's `queuePrev` must point to `tid`'s predecessor.
    This patches the interior links that `removeThreadFromQueue` does not handle.

    The splice reads the removed TCB's links from the **original** state (before
    mutations) to ensure consistent predecessor/successor identification. -/
private def spliceOutMidQueueNode (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
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

/-- WS-H2/H-05, R4-A.3 (M-12): Clean up external references to a TCB being retyped away.
    Removes the ThreadId from:
    1. The scheduler run queue (`removeRunnable`)
    2. All endpoint send/receive queues (`removeFromAllEndpointQueues`)
    3. All notification waiting lists (`removeFromAllNotificationWaitLists`)
    This prevents dangling-reference scenarios after a TCB is retyped. -/
def cleanupTcbReferences (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  let st := removeRunnable st tid
  let st := removeFromAllEndpointQueues st tid
  removeFromAllNotificationWaitLists st tid

-- ============================================================================
-- R4-A: Cleanup preservation theorems
-- ============================================================================

/-- T5-E: spliceOutMidQueueNode preserves the scheduler. The splice only
    modifies `objects`, so `{ st with objects := ... }.scheduler = st.scheduler`. -/
private theorem spliceOutMidQueueNode_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).scheduler = st.scheduler := by
  unfold spliceOutMidQueueNode; split <;> rfl

/-- T5-E: spliceOutMidQueueNode preserves lifecycle metadata. -/
private theorem spliceOutMidQueueNode_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).lifecycle = st.lifecycle := by
  unfold spliceOutMidQueueNode; split <;> rfl

/-- T5-E: spliceOutMidQueueNode preserves serviceRegistry. -/
private theorem spliceOutMidQueueNode_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).serviceRegistry = st.serviceRegistry := by
  unfold spliceOutMidQueueNode; split <;> rfl

/-- R4-A.1 + T5-E: removeFromAllEndpointQueues preserves the scheduler. -/
private theorem removeFromAllEndpointQueues_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).scheduler = st.scheduler := by
  have hSplice := spliceOutMidQueueNode_scheduler_eq st tid
  have key : ∀ (s : SystemState),
      (s.objects.fold s (fun acc oid obj =>
        match obj with
        | .endpoint ep =>
          let ep' : Endpoint := {
            sendQ := removeThreadFromQueue s ep.sendQ tid,
            receiveQ := removeThreadFromQueue s ep.receiveQ tid }
          { acc with objects := acc.objects.insert oid (.endpoint ep') }
        | _ => acc)).scheduler = s.scheduler :=
    fun s => SeLe4n.Kernel.RobinHood.RHTable.fold_preserves s.objects s _
      (fun acc => acc.scheduler = s.scheduler) rfl
      (fun acc _ _ hAcc => by split <;> exact hAcc)
  show (removeFromAllEndpointQueues st tid).scheduler = st.scheduler
  unfold removeFromAllEndpointQueues
  rw [key, hSplice]

/-- R4-A.2: removeFromAllNotificationWaitLists preserves the scheduler. -/
private theorem removeFromAllNotificationWaitLists_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllNotificationWaitLists st tid).scheduler = st.scheduler := by
  unfold removeFromAllNotificationWaitLists
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves st.objects st _
    (fun acc => acc.scheduler = st.scheduler) rfl
    (fun acc _ _ hAcc => by split <;> exact hAcc)

/-- R4-A.1 + T5-E: removeFromAllEndpointQueues preserves lifecycle metadata. -/
private theorem removeFromAllEndpointQueues_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).lifecycle = st.lifecycle := by
  have hSplice := spliceOutMidQueueNode_lifecycle_eq st tid
  have key : ∀ (s : SystemState),
      (s.objects.fold s (fun acc oid obj =>
        match obj with
        | .endpoint ep =>
          let ep' : Endpoint := {
            sendQ := removeThreadFromQueue s ep.sendQ tid,
            receiveQ := removeThreadFromQueue s ep.receiveQ tid }
          { acc with objects := acc.objects.insert oid (.endpoint ep') }
        | _ => acc)).lifecycle = s.lifecycle :=
    fun s => SeLe4n.Kernel.RobinHood.RHTable.fold_preserves s.objects s _
      (fun acc => acc.lifecycle = s.lifecycle) rfl
      (fun acc _ _ hAcc => by split <;> exact hAcc)
  show (removeFromAllEndpointQueues st tid).lifecycle = st.lifecycle
  unfold removeFromAllEndpointQueues
  rw [key, hSplice]

/-- R4-A.2: removeFromAllNotificationWaitLists preserves lifecycle metadata. -/
private theorem removeFromAllNotificationWaitLists_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllNotificationWaitLists st tid).lifecycle = st.lifecycle := by
  unfold removeFromAllNotificationWaitLists
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves st.objects st _
    (fun acc => acc.lifecycle = st.lifecycle) rfl
    (fun acc _ _ hAcc => by split <;> exact hAcc)

/-- R4-A.1 + T5-E: removeFromAllEndpointQueues preserves serviceRegistry. -/
private theorem removeFromAllEndpointQueues_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).serviceRegistry = st.serviceRegistry := by
  have hSplice := spliceOutMidQueueNode_serviceRegistry_eq st tid
  have key : ∀ (s : SystemState),
      (s.objects.fold s (fun acc oid obj =>
        match obj with
        | .endpoint ep =>
          let ep' : Endpoint := {
            sendQ := removeThreadFromQueue s ep.sendQ tid,
            receiveQ := removeThreadFromQueue s ep.receiveQ tid }
          { acc with objects := acc.objects.insert oid (.endpoint ep') }
        | _ => acc)).serviceRegistry = s.serviceRegistry :=
    fun s => SeLe4n.Kernel.RobinHood.RHTable.fold_preserves s.objects s _
      (fun acc => acc.serviceRegistry = s.serviceRegistry) rfl
      (fun acc _ _ hAcc => by split <;> exact hAcc)
  show (removeFromAllEndpointQueues st tid).serviceRegistry = st.serviceRegistry
  unfold removeFromAllEndpointQueues
  rw [key, hSplice]

/-- R4-A.2: removeFromAllNotificationWaitLists preserves serviceRegistry. -/
private theorem removeFromAllNotificationWaitLists_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllNotificationWaitLists st tid).serviceRegistry = st.serviceRegistry := by
  unfold removeFromAllNotificationWaitLists
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves st.objects st _
    (fun acc => acc.serviceRegistry = st.serviceRegistry) rfl
    (fun acc _ _ hAcc => by split <;> exact hAcc)

/-- After cleanup, the cleaned thread is not in the run queue. -/
theorem cleanupTcbReferences_removes_from_runnable
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    ¬(tid ∈ (cleanupTcbReferences st tid).scheduler.runQueue) := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_scheduler_eq]
  rw [removeFromAllEndpointQueues_scheduler_eq]
  unfold removeRunnable
  exact RunQueue.not_mem_remove_self _ _

/-- Cleanup preserves run queue membership for other threads. -/
theorem cleanupTcbReferences_preserves_runnable_ne
    (st : SystemState) (tid other : SeLe4n.ThreadId) (hNe : other ≠ tid)
    (hMem : other ∈ st.scheduler.runQueue) :
    other ∈ (cleanupTcbReferences st tid).scheduler.runQueue := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_scheduler_eq]
  rw [removeFromAllEndpointQueues_scheduler_eq]
  unfold removeRunnable
  rw [RunQueue.mem_remove]
  exact ⟨hMem, hNe⟩

/-- Cleanup preserves lifecycle metadata. -/
theorem cleanupTcbReferences_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).lifecycle = st.lifecycle := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_lifecycle_eq]
  exact removeFromAllEndpointQueues_lifecycle_eq (removeRunnable st tid) tid

/-- Cleanup preserves serviceRegistry. -/
theorem cleanupTcbReferences_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).serviceRegistry = st.serviceRegistry := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_serviceRegistry_eq]
  exact removeFromAllEndpointQueues_serviceRegistry_eq (removeRunnable st tid) tid

/-- CDT detach preserves the objects store. -/
private theorem detachSlotFromCdt_objects_eq (st : SystemState) (ref : SlotRef) :
    (SystemState.detachSlotFromCdt st ref).objects = st.objects := by
  unfold SystemState.detachSlotFromCdt; split <;> rfl

/-- CDT detach preserves lifecycle metadata. -/
private theorem detachSlotFromCdt_lifecycle_eq (st : SystemState) (ref : SlotRef) :
    (SystemState.detachSlotFromCdt st ref).lifecycle = st.lifecycle := by
  unfold SystemState.detachSlotFromCdt; split <;> rfl

/-- WS-H2/A-11: Detach all CDT slot references for a CNode being replaced.
    Iterates the CNode's slots and clears the cdtSlotNode/cdtNodeSlot
    bidirectional mappings for each slot, preventing orphaned CDT references. -/
def detachCNodeSlots (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) : SystemState :=
  cn.slots.fold st (fun acc slot _cap =>
    SystemState.detachSlotFromCdt acc { cnode := cnodeId, slot := slot }
  )

/-- `detachCNodeSlots` preserves the objects store (CDT-only operation). -/
theorem detachCNodeSlots_objects_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).objects = st.objects := by
  simp only [detachCNodeSlots]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots st _ (fun acc => acc.objects = st.objects)
    rfl (fun acc slot _cap hAcc => (detachSlotFromCdt_objects_eq acc
      { cnode := cnodeId, slot := slot }).trans hAcc)

/-- `detachCNodeSlots` preserves lifecycle metadata (CDT-only operation). -/
theorem detachCNodeSlots_lifecycle_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).lifecycle = st.lifecycle := by
  simp only [detachCNodeSlots]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots st _ (fun acc => acc.lifecycle = st.lifecycle)
    rfl (fun acc slot _cap hAcc => (detachSlotFromCdt_lifecycle_eq acc
      { cnode := cnodeId, slot := slot }).trans hAcc)

/-- WS-H2, R4-B.2 (M-13): Pre-retype cleanup combining TCB reference cleanup,
    CDT detach, and service registration cleanup.
    - If the current object is a TCB: clean up scheduler + IPC references.
    - If the current object is an endpoint: revoke service registrations
      backed by this endpoint to preserve `registryEndpointValid`.
    - If the current object is a CNode being replaced by a non-CNode: detach
      CDT slot mappings to prevent orphaned derivation tree references. -/
def lifecyclePreRetypeCleanup (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) : SystemState :=
  let st := match currentObj with
    | .tcb tcb => cleanupTcbReferences st tcb.tid
    | _ => st
  -- R4-B.2 (M-13): Clean up service registrations for endpoints being retyped
  let st := match currentObj with
    | .endpoint _ => cleanupEndpointServiceRegistrations st target
    | _ => st
  match currentObj with
  | .cnode cn =>
    match newObj with
    | .cnode _ => st  -- CNode → CNode: no CDT cleanup needed
    | _ => detachCNodeSlots st target cn
  | _ => st

/-- Pre-retype cleanup preserves the objects store for non-TCB cases.
    For TCB cases, objects are modified by endpoint/notification queue cleanup.
    For CNode→non-CNode, CDT detach does not change objects. -/
theorem lifecyclePreRetypeCleanup_objects_eq_non_tcb
    (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject)
    (hNotTcb : ∀ tcb, currentObj ≠ .tcb tcb) :
    (lifecyclePreRetypeCleanup st target currentObj newObj).objects = st.objects := by
  unfold lifecyclePreRetypeCleanup
  cases currentObj with
  | tcb tcb => exact absurd rfl (hNotTcb tcb)
  | cnode cn =>
    simp only []
    cases newObj <;> simp only [] <;>
    first | rfl | exact detachCNodeSlots_objects_eq st target cn
  | endpoint _ =>
    simp only []
    exact cleanupEndpointServiceRegistrations_objects_eq st target
  | notification _ | vspaceRoot _ | untyped _ => rfl

/-- Pre-retype cleanup preserves lifecycle metadata. -/
theorem lifecyclePreRetypeCleanup_lifecycle_eq
    (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) :
    (lifecyclePreRetypeCleanup st target currentObj newObj).lifecycle = st.lifecycle := by
  unfold lifecyclePreRetypeCleanup
  cases currentObj with
  | tcb tcb =>
    simp only []
    exact cleanupTcbReferences_lifecycle_eq st tcb.tid
  | cnode cn =>
    simp only []
    cases newObj <;> simp only [] <;>
    first | rfl | exact detachCNodeSlots_lifecycle_eq st target cn
  | endpoint _ =>
    simp only []
    exact cleanupEndpointServiceRegistrations_lifecycle_eq st target
  | notification _ | vspaceRoot _ | untyped _ => rfl


/-- Pre-retype cleanup only removes elements from the flat list, never adds. -/
private theorem cleanupTcbReferences_flat_subset
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (h : x ∈ (cleanupTcbReferences st tid).scheduler.runQueue.flat) :
    x ∈ st.scheduler.runQueue.flat := by
  unfold cleanupTcbReferences at h
  rw [removeFromAllNotificationWaitLists_scheduler_eq] at h
  rw [removeFromAllEndpointQueues_scheduler_eq] at h
  unfold removeRunnable at h
  simp only [] at h
  exact (List.mem_filter.mp h).1

/-- CDT cleanup preserves the scheduler. -/
private theorem detachCNodeSlots_scheduler_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).scheduler = st.scheduler := by
  simp only [detachCNodeSlots]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots st _ (fun acc => acc.scheduler = st.scheduler)
    rfl (fun acc slot _cap hAcc => by
      have : (SystemState.detachSlotFromCdt acc { cnode := cnodeId, slot := slot }).scheduler
          = acc.scheduler := by unfold SystemState.detachSlotFromCdt; split <;> rfl
      exact this.trans hAcc)

/-- Cleanup preserves the scheduler state. -/
private theorem cleanupTcbReferences_scheduler_eq_removeRunnable
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).scheduler = (removeRunnable st tid).scheduler := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_scheduler_eq]
  exact removeFromAllEndpointQueues_scheduler_eq (removeRunnable st tid) tid

/-- Pre-retype cleanup flat list subset: any element in the post-cleanup flat
    list was in the pre-cleanup flat list. -/
private theorem lifecyclePreRetypeCleanup_flat_subset
    (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) (x : SeLe4n.ThreadId)
    (h : x ∈ (lifecyclePreRetypeCleanup st target currentObj newObj).scheduler.runQueue.flat) :
    x ∈ st.scheduler.runQueue.flat := by
  unfold lifecyclePreRetypeCleanup at h
  cases currentObj with
  | tcb tcb =>
    simp only [] at h
    rw [cleanupTcbReferences_scheduler_eq_removeRunnable] at h
    unfold removeRunnable at h; simp only [] at h
    exact (List.mem_filter.mp h).1
  | cnode cn =>
    simp only [] at h
    cases newObj <;> simp only [] at h
    all_goals first
      | exact h
      | (have hSched := detachCNodeSlots_scheduler_eq st target cn
         rw [show (detachCNodeSlots st target cn).scheduler.runQueue.flat =
               st.scheduler.runQueue.flat from by rw [hSched]] at h
         exact h)
  | endpoint _ =>
    simp only [] at h
    rw [cleanupEndpointServiceRegistrations_scheduler_eq] at h
    exact h
  | notification _ | vspaceRoot _ | untyped _ => exact h

/-- **Internal building block — callers should use `lifecycleRetypeWithCleanup` instead.**

Retype an existing object id to a new typed object value.
This function skips `lifecyclePreRetypeCleanup` and `scrubObjectMemory`,
which means dangling references may persist and backing memory is not zeroed
(violating the H-05 safety guarantee and S6-C memory scrubbing guarantee).

T5-A (M-NEW-4): Marked as internal. All external retype operations must go
through `lifecycleRetypeWithCleanup` to ensure cleanup + scrubbing.

Deterministic branch contract for M4-A step 2:
1. target object must exist,
2. lifecycle metadata for the target id must agree with object-store type (`illegalState` otherwise),
3. authority slot lookup must succeed,
4. authority must satisfy `lifecycleRetypeAuthority` (`illegalAuthority` otherwise),
5. object store + lifecycle object-type metadata are updated atomically on success. -/
def lifecycleRetypeObject
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match st.objects[target]? with
    | none => .error .objectNotFound
    | some currentObj =>
        if st.lifecycle.objectTypes[target]? = some currentObj.objectType then
          match cspaceLookupSlot authority st with
          | .error e => .error e
          | .ok (authCap, st') =>
              if lifecycleRetypeAuthority authCap target then
                storeObject target newObj st'
              else
                .error .illegalAuthority
        else
          .error .illegalState

/-- Compose local revoke/delete cleanup with lifecycle retype.

Authority and state preconditions for deterministic success:
1. `authority ≠ cleanup` (delete-before-reuse ordering guard),
2. `cleanup` must resolve to a capability so revoke/delete can execute,
3. post-delete lookup of `cleanup` must return `invalidCapability`,
4. lifecycle retype preconditions from `lifecycleRetypeObject` must hold.

Failure branches remain explicit and ordered:
- aliasing `authority = cleanup` is rejected as `illegalState`,
- revoke/delete failures are propagated directly,
- unexpected post-delete lookup success is rejected as `illegalState`,
- final retype failures are propagated directly.

**S6-C note:** This is a low-level composition that does not perform memory
scrubbing. Callers requiring memory scrubbing (to prevent inter-domain
information leakage) should use `lifecycleRetypeWithCleanup`, which
integrates `scrubObjectMemory` between cleanup and retype. -/
def lifecycleRevokeDeleteRetype
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    if authority = cleanup then
      .error .illegalState
    else
      match cspaceRevoke cleanup st with
      | .error e => .error e
      | .ok (_, stRevoked) =>
          match cspaceDeleteSlot cleanup stRevoked with
          | .error e => .error e
          | .ok (_, stDeleted) =>
              match cspaceLookupSlot cleanup stDeleted with
              | .ok _ => .error .illegalState
              | .error .invalidCapability =>
                  lifecycleRetypeObject authority target newObj stDeleted
              | .error e => .error e

-- ============================================================================
-- WS-F2: Untyped Memory Model — retypeFromUntyped
-- ============================================================================

/-- WS-F2: Abstract allocation size for a kernel object type.
Used by `retypeFromUntyped` to determine how many bytes to carve from the
untyped region. These are abstract sizes for the formal model; a production
kernel would use architecture-specific values. -/
def objectTypeAllocSize : KernelObjectType → Nat
  | .tcb => 1024
  | .endpoint => 64
  | .notification => 64
  | .cnode => 4096
  | .vspaceRoot => 4096
  | .untyped => 4096

/-- S5-G: Predicate for object types that require page-aligned allocation bases.
VSpace roots and CNodes back page-table structures on ARM64, so their backing
memory must start on a 4KB page boundary. This matches seL4's alignment
requirement for page-table objects (seL4_PageTableObject, seL4_VSpaceObject). -/
def requiresPageAlignment : KernelObjectType → Bool
  | .vspaceRoot => true
  | .cnode => true
  | _ => false

/-- S5-G: Check whether the untyped allocation base (regionBase + watermark)
is page-aligned. Returns `true` when alignment is satisfied. -/
def allocationBasePageAligned (ut : UntypedObject) : Bool :=
  (ut.regionBase.toNat + ut.watermark) % 4096 == 0

-- ============================================================================
-- S6-C: Memory scrubbing on object deletion/retype
-- ============================================================================

/-- S6-C: Scrub backing memory for a deleted/retyped kernel object.

    Zeros the memory region that backed the old object, preventing information
    leakage when the memory is reallocated to a different security domain.
    The scrub region is determined by the object type's allocation size
    and a base address derived from the object ID.

    **Security rationale:** Without scrubbing, `retypeFromUntyped` could
    allocate a new object in memory that still contains data from a
    deleted object belonging to a different security domain. This violates
    non-interference even though the Lean-level object store is correctly
    updated, because the underlying machine memory retains the old data.

    **Abstract model note:** The base address is computed as
    `objectId.toNat × objectTypeAllocSize` — this is an abstract convention
    for the formal model. The hardware binding (WS-T) will use the actual
    physical addresses from the untyped allocator. -/
def scrubObjectMemory (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) : SystemState :=
  let size := objectTypeAllocSize objType
  let base : SeLe4n.PAddr := ⟨objectId.toNat * size⟩
  { st with machine := SeLe4n.zeroMemoryRange st.machine base size }

/-- S6-C: `scrubObjectMemory` preserves the object store. -/
theorem scrubObjectMemory_objects_eq (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    (scrubObjectMemory st objectId objType).objects = st.objects := rfl

/-- S6-C: `scrubObjectMemory` preserves the scheduler state. -/
theorem scrubObjectMemory_scheduler_eq (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    (scrubObjectMemory st objectId objType).scheduler = st.scheduler := rfl

/-- S6-C: `scrubObjectMemory` preserves lifecycle metadata. -/
theorem scrubObjectMemory_lifecycle_eq (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    (scrubObjectMemory st objectId objType).lifecycle = st.lifecycle := rfl

/-- S6-C: `scrubObjectMemory` preserves the TLB state. -/
theorem scrubObjectMemory_tlb_eq (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    (scrubObjectMemory st objectId objType).tlb = st.tlb := rfl

/-- S6-C: `scrubObjectMemory` establishes the `memoryZeroed` postcondition
    for the scrubbed region. -/
theorem scrubObjectMemory_establishes_memoryZeroed
    (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    let size := objectTypeAllocSize objType
    let base : SeLe4n.PAddr := ⟨objectId.toNat * size⟩
    SeLe4n.memoryZeroed (scrubObjectMemory st objectId objType).machine base size := by
  simp [scrubObjectMemory]
  exact SeLe4n.zeroMemoryRange_establishes_memoryZeroed st.machine _ _

/-- S6-C: `scrubObjectMemory` preserves the objectIndex. -/
theorem scrubObjectMemory_objectIndex_eq (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    (scrubObjectMemory st objectId objType).objectIndex = st.objectIndex := rfl

/-- S6-C: `scrubObjectMemory` preserves the objectIndexSet. -/
theorem scrubObjectMemory_objectIndexSet_eq (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    (scrubObjectMemory st objectId objType).objectIndexSet = st.objectIndexSet := rfl

/-- WS-F2: Retype a new typed object from an untyped memory region.

Deterministic branch contract:
1. The source object must exist and be an `UntypedObject` (`untypedTypeMismatch` otherwise).
2. Device untypeds cannot back typed kernel objects except other untypeds
   (`untypedDeviceRestriction` if violated).
3. The allocation size must be at least `objectTypeAllocSize` for the target type
   (`untypedAllocSizeTooSmall` otherwise).
4. S5-G: For VSpace roots and CNodes, the allocation base address
   (`regionBase + watermark`) must be page-aligned (4KB boundary).
   Returns `allocationMisaligned` if violated. This matches seL4's requirement
   that page-table backing memory be page-aligned.
5. Authority capability must target the untyped object and include `write` rights
   (`illegalAuthority` otherwise).
6. The requested allocation size must fit within the remaining region space
   (`untypedRegionExhausted` otherwise).
7. U-H02: Post-allocation alignment re-verification — after advancing the watermark,
   the new base must still be page-aligned for VSpace-bound objects
   (`allocationMisaligned` otherwise). This prevents non-page-aligned allocations
   from shifting subsequent allocations to unaligned bases.
8. On success: watermark is advanced, new child is recorded, and the new typed
   object is stored at `childId` via `storeObject`. -/
def retypeFromUntyped
    (authority : CSpaceAddr)
    (untypedId : SeLe4n.ObjId)
    (childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat) : Kernel Unit :=
  fun st =>
    match st.objects[untypedId]? with
    | none => .error .objectNotFound
    | some (.untyped ut) =>
        -- S4-B: Capacity check — reject allocation when object store is at capacity
        if st.objectIndex.length ≥ maxObjects then
          .error .objectStoreCapacityExceeded
        -- WS-H2/H-06: childId must not equal untypedId (self-overwrite guard)
        else if childId = untypedId then
          .error .childIdSelfOverwrite
        -- WS-H2/A-26: childId must not collide with an existing object
        else if st.objects[childId]?.isSome then
          .error .childIdCollision
        -- WS-H2/A-27: childId must not collide with an existing untyped child
        else if ut.children.any (fun c => c.objId == childId) then
          .error .childIdCollision
        -- Device untypeds cannot back typed kernel objects (except other untypeds)
        else if ut.isDevice && newObj.objectType != .untyped then
          .error .untypedDeviceRestriction
        -- Allocation size must be at least the minimum for the target object type
        else if allocSize < objectTypeAllocSize newObj.objectType then
          .error .untypedAllocSizeTooSmall
        -- S5-G: Page-alignment check for VSpace-bound objects
        else if requiresPageAlignment newObj.objectType && !allocationBasePageAligned ut then
          .error .allocationMisaligned
        else
          match cspaceLookupSlot authority st with
          | .error e => .error e
          | .ok (authCap, st') =>
              if lifecycleRetypeAuthority authCap untypedId then
                -- WS-H2/A-28: Both objects are computed before any state mutation.
                -- `ut'` and `newObj` are fully determined at this point.
                match ut.allocate childId allocSize with
                | none => .error .untypedRegionExhausted
                | some (ut', _offset) =>
                    -- U-H02: Post-allocation alignment re-verification.
                    -- After advancing the watermark by `allocSize`, the new base
                    -- (`regionBase + watermark'`) must remain page-aligned if the
                    -- object type requires it. Non-page-aligned allocations would
                    -- shift subsequent allocations to unaligned bases, violating S5-G.
                    if requiresPageAlignment newObj.objectType && !allocationBasePageAligned ut' then
                      .error .allocationMisaligned
                    else
                    -- Atomic dual-store: untyped watermark advance + child creation
                    match storeObject untypedId (.untyped ut') st' with
                    | .error e => .error e
                    | .ok ((), stUt) =>
                        storeObject childId newObj stUt
              else
                .error .illegalAuthority
    | some _ => .error .untypedTypeMismatch

/-- WS-F2: Helper to look up an UntypedObject by ObjId. -/
def lookupUntyped (st : SystemState) (id : SeLe4n.ObjId) : Option UntypedObject :=
  match st.objects[id]? with
  | some (.untyped ut) => some ut
  | _ => none

/-- WS-F2: Decomposition of a successful `retypeFromUntyped` into constituent steps.
S5-G: The alignment check is an additional error guard (returns `allocationMisaligned`
for VSpace/CNode objects on unaligned bases); it does not affect the decomposition
since success implies the guard passed. -/
theorem retypeFromUntyped_ok_decompose
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    ∃ ut ut' cap stLookup stUt offset,
      st.objects[untypedId]? = some (.untyped ut) ∧
      (ut.isDevice = false ∨ newObj.objectType = .untyped) ∧
      ¬(allocSize < objectTypeAllocSize newObj.objectType) ∧
      cspaceLookupSlot authority st = .ok (cap, stLookup) ∧
      lifecycleRetypeAuthority cap untypedId = true ∧
      ut.allocate childId allocSize = some (ut', offset) ∧
      storeObject untypedId (.untyped ut') stLookup = .ok ((), stUt) ∧
      storeObject childId newObj stUt = .ok ((), st') := by
  unfold retypeFromUntyped at hStep
  cases hObj : st.objects[untypedId]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ => simp [hObj] at hStep
      | endpoint _ => simp [hObj] at hStep
      | notification _ => simp [hObj] at hStep
      | cnode _ => simp [hObj] at hStep
      | vspaceRoot _ => simp [hObj] at hStep
      | untyped ut =>
          simp only [hObj] at hStep
          -- S4-B: Discharge capacity check
          have hCapOk : ¬(st.objectIndex.length ≥ maxObjects) := by
            intro h; simp [h] at hStep
          simp only [hCapOk, ↓reduceIte] at hStep
          -- WS-H2: Discharge childId safety guards (each .error contradicts .ok)
          have hNeSelf : childId ≠ untypedId := by
            intro h; simp [h] at hStep
          have hCollF : st.objects[childId]?.isSome = false := by
            cases h : st.objects[childId]?.isSome
            · rfl
            · simp [hNeSelf, h] at hStep
          have hFrF : (ut.children.any fun c => c.objId == childId) = false := by
            cases h : ut.children.any (fun c => c.objId == childId)
            · rfl
            · simp [hNeSelf, hCollF, h] at hStep
          simp only [hNeSelf, hCollF, hFrF, ↓reduceIte] at hStep
          -- S5-G: The function now has an alignment check between allocSz and cspaceLookup.
          -- We discharge all early guards (device, allocSz, alignment) uniformly, leaving
          -- the cspaceLookup → authority → allocate → storeObject chain for extraction.
          -- S5-G: Helper — all early guards (device, allocSz, alignment) are
          -- discharged uniformly. The alignment check is a new if-then-else
          -- between allocSz and cspaceLookup.
          -- Strategy: rewrite retypeFromUntyped as a chain of nested matches,
          -- use `omega`/`simp`/`split` to navigate each guard to contradiction or success.
          cases hDevBool : ut.isDevice <;> simp only [hDevBool] at hStep
          · -- ut.isDevice = false: device check trivially passes
            simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hStep
            by_cases hAllocSz : allocSize < objectTypeAllocSize newObj.objectType
            · simp [hAllocSz] at hStep
            · simp only [hAllocSz, ↓reduceIte] at hStep
              -- S5-G: split on alignment condition
              split at hStep
              · simp at hStep
              · cases hLookup : cspaceLookupSlot authority st with
                | error e => simp [hLookup] at hStep
                | ok pair =>
                    rcases pair with ⟨cap, stLookup⟩
                    simp [hLookup] at hStep
                    by_cases hAuth : lifecycleRetypeAuthority cap untypedId
                    · simp [hAuth] at hStep
                      cases hAlloc : UntypedObject.allocate ut childId allocSize with
                      | none => simp [hAlloc] at hStep
                      | some result =>
                          rcases result with ⟨ut', offset⟩
                          simp [hAlloc] at hStep
                          -- U-H02: split on post-allocation alignment check
                          split at hStep
                          · simp at hStep
                          · cases hStoreUt : storeObject untypedId (.untyped ut') stLookup with
                            | error e => simp [hStoreUt] at hStep
                            | ok pair2 =>
                                rcases pair2 with ⟨_, stUt⟩
                                simp [hStoreUt] at hStep
                                exact ⟨ut, ut', cap, stLookup, stUt, offset, rfl, Or.inl hDevBool, hAllocSz, rfl, hAuth, hAlloc, hStoreUt, hStep⟩
                    · simp [hAuth] at hStep
          · -- ut.isDevice = true: need objectType check
            by_cases hObjType : newObj.objectType = KernelObjectType.untyped
            · -- objectType = untyped: device check passes
              have hBne : (newObj.objectType != KernelObjectType.untyped) = false := by
                simp [bne, hObjType]
              simp [hBne] at hStep
              by_cases hAllocSz : allocSize < objectTypeAllocSize newObj.objectType
              · simp [hAllocSz] at hStep
              · simp only [hAllocSz, ↓reduceIte] at hStep
                -- S5-G: split on alignment condition
                split at hStep
                · simp at hStep
                · cases hLookup : cspaceLookupSlot authority st with
                  | error e => simp [hLookup] at hStep
                  | ok pair =>
                      rcases pair with ⟨cap, stLookup⟩
                      simp [hLookup] at hStep
                      by_cases hAuth : lifecycleRetypeAuthority cap untypedId
                      · simp [hAuth] at hStep
                        cases hAlloc : UntypedObject.allocate ut childId allocSize with
                        | none => simp [hAlloc] at hStep
                        | some result =>
                            rcases result with ⟨ut', offset⟩
                            simp [hAlloc] at hStep
                            -- U-H02: split on post-allocation alignment check
                            split at hStep
                            · simp at hStep
                            · cases hStoreUt : storeObject untypedId (.untyped ut') stLookup with
                              | error e => simp [hStoreUt] at hStep
                              | ok pair2 =>
                                  rcases pair2 with ⟨_, stUt⟩
                                  simp [hStoreUt] at hStep
                                  exact ⟨ut, ut', cap, stLookup, stUt, offset,
                                    rfl, Or.inr hObjType, hAllocSz, rfl, hAuth, hAlloc, hStoreUt, hStep⟩
                      · simp [hAuth] at hStep
            · -- objectType != untyped: device restriction fires -> contradiction
              have hBne : (newObj.objectType != KernelObjectType.untyped) = true := by
                simp [bne, hObjType]
              simp [hBne] at hStep

/-- WS-F2: `retypeFromUntyped` returns `untypedTypeMismatch` when the source is not an untyped. -/
theorem retypeFromUntyped_error_typeMismatch
    (st : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (newObj : KernelObject)
    (allocSize : Nat) (obj : KernelObject)
    (hObj : st.objects[untypedId]? = some obj)
    (hNotUntyped : ∀ u, obj ≠ .untyped u) :
    retypeFromUntyped authority untypedId childId newObj allocSize st = .error .untypedTypeMismatch := by
  unfold retypeFromUntyped
  cases obj with
  | untyped u => exact absurd rfl (hNotUntyped u)
  | tcb _ => simp [hObj]
  | endpoint _ => simp [hObj]
  | notification _ => simp [hObj]
  | cnode _ => simp [hObj]
  | vspaceRoot _ => simp [hObj]


/-- WS-F2: `retypeFromUntyped` returns `untypedAllocSizeTooSmall` when allocSize is insufficient. -/
theorem retypeFromUntyped_error_allocSizeTooSmall
    (st : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (newObj : KernelObject)
    (allocSize : Nat) (ut : UntypedObject)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hCapOk : st.objectIndex.length < maxObjects)
    (hNeSelf : childId ≠ untypedId)
    (hNoCollision : st.objects[childId]?.isSome = false)
    (hFreshChildren : ut.children.any (fun c => c.objId == childId) = false)
    (hNotDev : ut.isDevice = false ∨ newObj.objectType = .untyped)
    (hSmall : allocSize < objectTypeAllocSize newObj.objectType) :
    retypeFromUntyped authority untypedId childId newObj allocSize st =
      .error .untypedAllocSizeTooSmall := by
  unfold retypeFromUntyped
  have hCapF : ¬(st.objectIndex.length ≥ maxObjects) := by omega
  simp [hObj, hCapF, hNeSelf, hNoCollision, hFreshChildren]
  cases hNotDev with
  | inl hFalse => simp [hFalse, hSmall]
  | inr hUt =>
      rw [hUt] at hSmall
      by_cases hDevBool : ut.isDevice
      · simp [hDevBool, hUt, hSmall]
      · simp [hDevBool, hUt, hSmall]

/-- WS-F2: `retypeFromUntyped` returns `untypedRegionExhausted` when allocation cannot fit.
S5-G: Alignment check must pass (or type doesn't require it) for this error to be reached. -/
theorem retypeFromUntyped_error_regionExhausted
    (st : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (newObj : KernelObject)
    (allocSize : Nat) (ut : UntypedObject) (cap : Capability)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hCapOk : st.objectIndex.length < maxObjects)
    (hNeSelf : childId ≠ untypedId)
    (hNoCollision : st.objects[childId]?.isSome = false)
    (hFreshChildren : ut.children.any (fun c => c.objId == childId) = false)
    (hNotDev : ut.isDevice = false ∨ newObj.objectType = .untyped)
    (hAllocSzOk : ¬(allocSize < objectTypeAllocSize newObj.objectType))
    (hAlignOk : (requiresPageAlignment newObj.objectType && !allocationBasePageAligned ut) = false)
    (hLookup : cspaceLookupSlot authority st = .ok (cap, st))
    (hAuth : lifecycleRetypeAuthority cap untypedId = true)
    (hNoFit : ut.allocate childId allocSize = none) :
    retypeFromUntyped authority untypedId childId newObj allocSize st =
      .error .untypedRegionExhausted := by
  unfold retypeFromUntyped
  have hCapF : ¬(st.objectIndex.length ≥ maxObjects) := by omega
  simp only [hObj, hCapF, ↓reduceIte, hNeSelf, hNoCollision, hFreshChildren]
  cases hNotDev with
  | inl hFalse =>
      simp only [hFalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hAllocSzOk, hAlignOk,
        ↓reduceIte, hLookup, hAuth, hNoFit]
  | inr hUt =>
      by_cases hDevBool : ut.isDevice
      · have hBne : (newObj.objectType != KernelObjectType.untyped) = false := by
          simp [bne, hUt]
        simp only [hDevBool, hBne, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
          hAllocSzOk, hAlignOk, ↓reduceIte, hLookup, hAuth, hNoFit]
      · simp only [hDevBool, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          hAllocSzOk, hAlignOk, ↓reduceIte, hLookup, hAuth, hNoFit]

/- Local lifecycle transition helper lemmas (M4-A step 4).
These theorems keep preservation scripts focused on invariant obligations rather than
repeating transition case analysis. -/

theorem lifecycle_storeObject_objects_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[id]? = some obj :=
  SeLe4n.Model.storeObject_objects_eq st st' id obj hObjInv hStore

theorem lifecycle_storeObject_objects_ne
    (st st' : SystemState)
    (id oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hNe : oid ≠ id)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[oid]? = st.objects[oid]? :=
  SeLe4n.Model.storeObject_objects_ne st st' id oid obj hNe hObjInv hStore

theorem lifecycle_storeObject_scheduler_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler :=
  SeLe4n.Model.storeObject_scheduler_eq st st' id obj hStore

theorem cspaceLookupSlot_ok_state_eq
    (st : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (st' : SystemState)
    (hLookup : cspaceLookupSlot addr st = .ok (cap, st')) :
    st' = st := by
  unfold cspaceLookupSlot at hLookup
  cases hCap : SystemState.lookupSlotCap st addr with
  | none =>
      cases hObj : st.objects[addr.cnode]? with
      | none => simp [hCap, hObj] at hLookup
      | some obj =>
          cases obj <;> simp [hCap, hObj] at hLookup
  | some cap' =>
      simp [hCap] at hLookup
      exact hLookup.2.symm


theorem lifecycleRetypeObject_ok_as_storeObject
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    ∃ currentObj cap,
      st.objects[target]? = some currentObj ∧
      st.lifecycle.objectTypes[target]? = some currentObj.objectType ∧
      cspaceLookupSlot authority st = .ok (cap, st) ∧
      lifecycleRetypeAuthority cap target = true ∧
      storeObject target newObj st = .ok ((), st') := by
  unfold lifecycleRetypeObject at hStep
  cases hObj : st.objects[target]? with
  | none => simp [hObj] at hStep
  | some currentObj =>
      by_cases hMeta : st.lifecycle.objectTypes[target]? = some currentObj.objectType
      · cases hLookup : cspaceLookupSlot authority st with
        | error e => simp [hObj, hMeta, hLookup] at hStep
        | ok pair =>
            rcases pair with ⟨cap, stLookup⟩
            cases hAuth : lifecycleRetypeAuthority cap target with
            | false => simp [hObj, hMeta, hLookup, hAuth] at hStep
            | true =>
                have hLookupSt : stLookup = st :=
                  cspaceLookupSlot_ok_state_eq st authority cap stLookup hLookup
                subst hLookupSt
                simp [hObj, hMeta, hLookup, hAuth] at hStep
                exact ⟨currentObj, cap, by simp, hMeta, by simp, hAuth, hStep⟩
      · simp [hObj, hMeta] at hStep

theorem lifecycleRetypeObject_ok_lookup_preserved_ne
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target oid : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hNe : oid ≠ target)
    (hObjInv : st.objects.invExt)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    st'.objects[oid]? = st.objects[oid]? := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  exact lifecycle_storeObject_objects_ne st st' target oid newObj hNe hObjInv hStore

theorem lifecycleRetypeObject_ok_runnable_membership
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (tid : SeLe4n.ThreadId)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st'))
    (hRun : tid ∈ st'.scheduler.runnable) :
    tid ∈ st.scheduler.runnable := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  have hSchedEq : st'.scheduler = st.scheduler :=
    lifecycle_storeObject_scheduler_eq st st' target newObj hStore
  simpa [hSchedEq] using hRun

theorem lifecycleRetypeObject_ok_not_runnable_membership
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (tid : SeLe4n.ThreadId)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st'))
    (hNotRun : tid ∉ st.scheduler.runnable) :
    tid ∉ st'.scheduler.runnable := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  have hSchedEq : st'.scheduler = st.scheduler :=
    lifecycle_storeObject_scheduler_eq st st' target newObj hStore
  simpa [hSchedEq] using hNotRun

theorem lifecycleRetypeObject_error_illegalState
    (st : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj currentObj : KernelObject)
    (hObj : st.objects[target]? = some currentObj)
    (hMetaMismatch : st.lifecycle.objectTypes[target]? ≠ some currentObj.objectType) :
    lifecycleRetypeObject authority target newObj st = .error .illegalState := by
  unfold lifecycleRetypeObject
  simp [hObj, hMetaMismatch]

theorem lifecycleRetypeObject_error_illegalAuthority
    (st : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj currentObj : KernelObject)
    (cap : Capability)
    (hObj : st.objects[target]? = some currentObj)
    (hMeta : st.lifecycle.objectTypes[target]? = some currentObj.objectType)
    (hLookup : cspaceLookupSlot authority st = .ok (cap, st))
    (hAuthFail : lifecycleRetypeAuthority cap target = false) :
    lifecycleRetypeObject authority target newObj st = .error .illegalAuthority := by
  unfold lifecycleRetypeObject
  simp [hObj, hMeta, hLookup, hAuthFail]


theorem lifecycleRetypeObject_success_updates_object
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj currentObj : KernelObject)
    (cap : Capability)
    (hObj : st.objects[target]? = some currentObj)
    (hMeta : st.lifecycle.objectTypes[target]? = some currentObj.objectType)
    (hLookup : cspaceLookupSlot authority st = .ok (cap, st))
    (hAuth : lifecycleRetypeAuthority cap target = true)
    (hObjInv : st.objects.invExt)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    st'.objects[target]? = some newObj := by
  have _ : st.lifecycle.objectTypes[target]? = some currentObj.objectType := hMeta
  have _ : lifecycleRetypeAuthority cap target = true := hAuth
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨currentObj', cap', hObj', _, hLookup', _, hStore⟩
  have hCurrent : currentObj' = currentObj := by
    apply Option.some.inj
    rw [← hObj', hObj]
  subst hCurrent
  have hCapLookup' : SystemState.lookupSlotCap st authority = some cap' :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st authority cap').1 hLookup'
  have hCapLookup : SystemState.lookupSlotCap st authority = some cap :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st authority cap).1 hLookup
  rw [hCapLookup'] at hCapLookup
  injection hCapLookup with hCapEq
  subst hCapEq
  exact lifecycle_storeObject_objects_eq st st' target newObj hObjInv hStore

theorem lifecycleRevokeDeleteRetype_error_authority_cleanup_alias
    (st : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hAlias : authority = cleanup) :
    lifecycleRevokeDeleteRetype authority cleanup target newObj st = .error .illegalState := by
  unfold lifecycleRevokeDeleteRetype
  simp [hAlias]

theorem lifecycleRevokeDeleteRetype_ok_implies_authority_ne_cleanup
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    authority ≠ cleanup := by
  intro hAlias
  have hErr := lifecycleRevokeDeleteRetype_error_authority_cleanup_alias
    st authority cleanup target newObj hAlias
  rw [hErr] at hStep
  cases hStep

theorem lifecycleRevokeDeleteRetype_ok_implies_staged_steps
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    ∃ stRevoked stDeleted,
      authority ≠ cleanup ∧
      cspaceRevoke cleanup st = .ok ((), stRevoked) ∧
      cspaceDeleteSlot cleanup stRevoked = .ok ((), stDeleted) ∧
      cspaceLookupSlot cleanup stDeleted = .error .invalidCapability ∧
      lifecycleRetypeObject authority target newObj stDeleted = .ok ((), st') := by
  by_cases hAlias : authority = cleanup
  · have hErr : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .error .illegalState := by
      simp [lifecycleRevokeDeleteRetype, hAlias]
    rw [hErr] at hStep
    cases hStep
  · cases hRevoke : cspaceRevoke cleanup st with
    | error e =>
        simp [lifecycleRevokeDeleteRetype, hAlias, hRevoke] at hStep
    | ok revPair =>
        cases revPair with
        | mk revUnit stRevoked =>
            cases revUnit
            cases hDelete : cspaceDeleteSlot cleanup stRevoked with
            | error e =>
                simp [lifecycleRevokeDeleteRetype, hAlias, hRevoke, hDelete] at hStep
            | ok delPair =>
                cases delPair with
                | mk delUnit stDeleted =>
                    cases delUnit
                    cases hLookup : cspaceLookupSlot cleanup stDeleted with
                    | ok pair =>
                        simp [lifecycleRevokeDeleteRetype, hAlias, hRevoke, hDelete, hLookup] at hStep
                    | error err =>
                        have hErr : err = .invalidCapability := by
                          cases err <;> simp [lifecycleRevokeDeleteRetype, hAlias, hRevoke, hDelete, hLookup] at hStep
                          rfl
                        subst hErr
                        refine ⟨stRevoked, stDeleted, hAlias, ?_, ?_, ?_, ?_⟩
                        · rfl
                        · simpa using hDelete
                        · exact hLookup
                        · simpa [lifecycleRevokeDeleteRetype, hAlias, hRevoke, hDelete, hLookup] using hStep


-- ============================================================================
-- WS-H2/S6-C: Safe lifecycle retype wrapper (cleanup + scrub + retype)
-- ============================================================================

/-- WS-H2/S6-C: Safe lifecycle retype with reference cleanup and memory scrubbing.
    Composes three phases:
    1. `lifecyclePreRetypeCleanup` — TCB scheduler dequeue + CNode CDT detach
    2. `scrubObjectMemory` — zero the backing memory of the old object (S6-C)
    3. `lifecycleRetypeObject` — replace the object in the store

    The cleanup runs on the pre-retype state; scrubbing zeros machine memory
    to prevent information leakage between security domains; the actual retype
    operates on the cleaned+scrubbed state.

    Since cleanup and scrubbing preserve `objects` and `lifecycle`, the retype
    authority check and lifecycle metadata check succeed on the scrubbed state
    iff they succeed on the original state.

    This wrapper is the recommended entry point for callers that need the
    H-05 safety guarantee and S6-C memory scrubbing guarantee.

    T5-D (M-NEW-5): Validates `KernelObject.wellFormed` for the new object before
    retype. Returns `illegalState` if the new object fails well-formedness
    (e.g., TCB with dangling cspaceRoot/vspaceRoot, CNode with out-of-range guard).
    The API layer (register decode + typed argument construction) is designed to
    produce well-formed objects, so this check is a defense-in-depth measure. -/
def lifecycleRetypeWithCleanup
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    -- T5-D: Validate new object well-formedness before proceeding
    if ¬ newObj.wellFormed st.objects then
      .error .illegalState
    else
      match st.objects[target]? with
      | none => lifecycleRetypeObject authority target newObj st
      | some currentObj =>
          let stClean := lifecyclePreRetypeCleanup st target currentObj newObj
          -- S6-C: Scrub backing memory before retype to prevent info leakage
          let stScrubbed := scrubObjectMemory stClean target currentObj.objectType
          lifecycleRetypeObject authority target newObj stScrubbed

/-- WS-H2/H-05/S6-C: After a TCB retype via the safe wrapper, the old ThreadId is
    not in the run queue.  This is the key safety property required by H-05.
    The proof threads through both cleanup and scrubbing phases, using the fact
    that `scrubObjectMemory` preserves the scheduler state. -/
theorem lifecycleRetypeWithCleanup_ok_runnable_no_dangling
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (tcb : TCB)
    (hObj : st.objects[target]? = some (.tcb tcb))
    (hStep : lifecycleRetypeWithCleanup authority target newObj st = .ok ((), st')) :
    ¬(tcb.tid ∈ st'.scheduler.runQueue) := by
  unfold lifecycleRetypeWithCleanup at hStep
  -- T5-D: wellFormed guard — since hStep is .ok, the guard must have passed
  simp only [] at hStep
  split at hStep
  · contradiction
  · rename_i hWF
    simp only [hObj] at hStep
    -- hStep now has lifecycleRetypeObject on the scrubbed+cleaned state
    rcases lifecycleRetypeObject_ok_as_storeObject _ st' authority target newObj hStep with
      ⟨_, _, _, _, _, _, hStore⟩
    have hSchedEq : st'.scheduler =
        (scrubObjectMemory (lifecyclePreRetypeCleanup st target (.tcb tcb) newObj)
          target (KernelObject.tcb tcb).objectType).scheduler :=
      lifecycle_storeObject_scheduler_eq _ st' target newObj hStore
    rw [hSchedEq, scrubObjectMemory_scheduler_eq]
    unfold lifecyclePreRetypeCleanup
    simp only []
    exact cleanupTcbReferences_removes_from_runnable st tcb.tid

-- ============================================================================
-- WS-K-D: Lifecycle syscall dispatch helpers
-- ============================================================================

/-- WS-K-D: Map a raw type tag and size hint to a default `KernelObject`.

Tag encoding follows `KernelObjectType` ordinal order:
- 0 = TCB, 1 = Endpoint, 2 = Notification, 3 = CNode, 4 = VSpaceRoot, 5 = Untyped.

The size hint is used only for untyped objects (as `regionSize`); other types
ignore it. All constructed objects use field defaults — the retype operation
creates an identity; subsequent operations configure the object. -/
def objectOfTypeTag (typeTag : Nat) (sizeHint : Nat)
    : Except KernelError KernelObject :=
  match typeTag with
  | 0 => .ok (.tcb {
      tid := SeLe4n.ThreadId.ofNat 0
      priority := SeLe4n.Priority.ofNat 0
      domain := SeLe4n.DomainId.ofNat 0
      cspaceRoot := SeLe4n.ObjId.ofNat 0
      vspaceRoot := SeLe4n.ObjId.ofNat 0
      ipcBuffer := SeLe4n.VAddr.ofNat 0
    })
  | 1 => .ok (.endpoint { sendQ := {}, receiveQ := {} })
  | 2 => .ok (.notification {
      state := .idle, waitingThreads := [], pendingBadge := none
    })
  | 3 => .ok (.cnode {
      depth := 0, guardWidth := 0, guardValue := 0,
      radixWidth := 0, slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16
    })
  | 4 => .ok (.vspaceRoot {
      asid := SeLe4n.ASID.ofNat 0, mappings := {}
    })
  | 5 => .ok (.untyped {
      regionBase := SeLe4n.PAddr.ofNat 0,
      regionSize := sizeHint,
      watermark := 0,
      children := [],
      isDevice := false
    })
  | _ + 6 => .error .invalidTypeTag

/-- WS-K-D: `objectOfTypeTag` fails iff the tag exceeds 5. -/
theorem objectOfTypeTag_error_iff (tag : Nat) (size : Nat) :
    (∃ e, objectOfTypeTag tag size = .error e) ↔ tag > 5 := by
  constructor
  · intro ⟨e, h⟩
    unfold objectOfTypeTag at h
    match tag with
    | 0 | 1 | 2 | 3 | 4 | 5 => simp at h
    | n + 6 => omega
  · intro h
    unfold objectOfTypeTag
    match tag, h with
    | n + 6, _ => exact ⟨.invalidTypeTag, rfl⟩

/-- WS-K-D: Successful results have the expected `KernelObjectType`. -/
theorem objectOfTypeTag_type (tag : Nat) (size : Nat) (obj : KernelObject)
    (hOk : objectOfTypeTag tag size = .ok obj) :
    (tag = 0 → obj.objectType = .tcb) ∧
    (tag = 1 → obj.objectType = .endpoint) ∧
    (tag = 2 → obj.objectType = .notification) ∧
    (tag = 3 → obj.objectType = .cnode) ∧
    (tag = 4 → obj.objectType = .vspaceRoot) ∧
    (tag = 5 → obj.objectType = .untyped) := by
  unfold objectOfTypeTag at hOk
  match tag with
  | 0 => simp at hOk; subst hOk; simp [KernelObject.objectType]
  | 1 => simp at hOk; subst hOk; simp [KernelObject.objectType]
  | 2 => simp at hOk; subst hOk; simp [KernelObject.objectType]
  | 3 => simp at hOk; subst hOk; simp [KernelObject.objectType]
  | 4 => simp at hOk; subst hOk; simp [KernelObject.objectType]
  | 5 => simp at hOk; subst hOk; simp [KernelObject.objectType]
  | _ + 6 => simp at hOk

/-- R7-E/L-10: Typed version of `objectOfTypeTag` that takes `KernelObjectType` directly.
    Eliminates the invalid-tag error path since the type is already validated. -/
def objectOfKernelType (objType : KernelObjectType) (sizeHint : Nat) : KernelObject :=
  match objType with
  | .tcb => .tcb {
      tid := SeLe4n.ThreadId.ofNat 0
      priority := SeLe4n.Priority.ofNat 0
      domain := SeLe4n.DomainId.ofNat 0
      cspaceRoot := SeLe4n.ObjId.ofNat 0
      vspaceRoot := SeLe4n.ObjId.ofNat 0
      ipcBuffer := SeLe4n.VAddr.ofNat 0
    }
  | .endpoint => .endpoint { sendQ := {}, receiveQ := {} }
  | .notification => .notification {
      state := .idle, waitingThreads := [], pendingBadge := none
    }
  | .cnode => .cnode {
      depth := 0, guardWidth := 0, guardValue := 0,
      radixWidth := 0, slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16
    }
  | .vspaceRoot => .vspaceRoot {
      asid := SeLe4n.ASID.ofNat 0, mappings := {}
    }
  | .untyped => .untyped {
      regionBase := SeLe4n.PAddr.ofNat 0,
      regionSize := sizeHint,
      watermark := 0,
      children := [],
      isDevice := false
    }

/-- R7-E/L-10: `objectOfKernelType` produces an object of the requested type. -/
theorem objectOfKernelType_type (objType : KernelObjectType) (sizeHint : Nat) :
    (objectOfKernelType objType sizeHint).objectType = objType := by
  cases objType <;> simp [objectOfKernelType, KernelObject.objectType]

/-- R7-E/L-10: `objectOfKernelType` agrees with `objectOfTypeTag` on valid tags. -/
theorem objectOfKernelType_eq_objectOfTypeTag (objType : KernelObjectType) (sizeHint : Nat) :
    objectOfTypeTag objType.toNat sizeHint = .ok (objectOfKernelType objType sizeHint) := by
  cases objType <;> simp [objectOfKernelType, objectOfTypeTag, KernelObjectType.toNat]

-- ============================================================================
-- WS-K-D: lifecycleRetypeDirect — pre-resolved authority variant
-- ============================================================================

/-- **Internal building block — callers should use `lifecycleRetypeDirectWithCleanup` instead.**

WS-K-D: Retype with a pre-resolved authority capability.
Companion to `lifecycleRetypeObject` for the register-sourced dispatch
path where the authority cap has already been resolved by `syscallInvoke`.

T5-B (M-NEW-4): Marked as internal. This function takes a pre-resolved
`Capability` and bypasses cleanup and memory scrubbing. External callers
must use `lifecycleRetypeDirectWithCleanup` (for pre-resolved caps) or
`lifecycleRetypeWithCleanup` (for CSpaceAddr) for the H-05 and S6-C
guarantees. U-H04: API dispatch now routes through the safe wrapper.

Deterministic branch contract:
1. Target object must exist (`objectNotFound` otherwise).
2. Lifecycle metadata must agree with object-store type (`illegalState`).
3. Authority cap must satisfy `lifecycleRetypeAuthority` — targets the
   object with `.retype` right (`illegalAuthority` otherwise).
4. Object store is updated atomically on success via `storeObject`. -/
def lifecycleRetypeDirect
    (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match st.objects[target]? with
    | none => .error .objectNotFound
    | some currentObj =>
        if st.lifecycle.objectTypes[target]? = some currentObj.objectType then
          if lifecycleRetypeAuthority authCap target then
            storeObject target newObj st
          else
            .error .illegalAuthority
        else
          .error .illegalState

/-- WS-K-D: When `cspaceLookupSlot` resolves to `(cap, st)` (state unchanged),
`lifecycleRetypeDirect` with that cap equals `lifecycleRetypeObject` with the
authority address. -/
theorem lifecycleRetypeDirect_eq_lifecycleRetypeObject
    (authority : CSpaceAddr) (authCap : Capability)
    (target : SeLe4n.ObjId) (newObj : KernelObject) (st : SystemState)
    (hLookup : cspaceLookupSlot authority st = .ok (authCap, st)) :
    lifecycleRetypeDirect authCap target newObj st =
    lifecycleRetypeObject authority target newObj st := by
  unfold lifecycleRetypeDirect lifecycleRetypeObject
  cases hObj : st.objects[target]? with
  | none => rfl
  | some currentObj =>
      by_cases hMeta : st.lifecycle.objectTypes[target]? = some currentObj.objectType
      · simp [hMeta, hLookup]
      · simp [hMeta]

/-- WS-K-D: `lifecycleRetypeDirect` returns `objectNotFound` when target missing. -/
theorem lifecycleRetypeDirect_error_objectNotFound
    (cap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState)
    (hNone : st.objects[target]? = none) :
    lifecycleRetypeDirect cap target newObj st = .error .objectNotFound := by
  unfold lifecycleRetypeDirect; simp [hNone]

/-- WS-K-D: `lifecycleRetypeDirect` returns `illegalState` on metadata mismatch. -/
theorem lifecycleRetypeDirect_error_illegalState
    (cap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState) (currentObj : KernelObject)
    (hSome : st.objects[target]? = some currentObj)
    (hMeta : st.lifecycle.objectTypes[target]? ≠ some currentObj.objectType) :
    lifecycleRetypeDirect cap target newObj st = .error .illegalState := by
  unfold lifecycleRetypeDirect; simp [hSome, hMeta]

/-- WS-K-D: `lifecycleRetypeDirect` returns `illegalAuthority` when auth check fails. -/
theorem lifecycleRetypeDirect_error_illegalAuthority
    (cap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState) (currentObj : KernelObject)
    (hSome : st.objects[target]? = some currentObj)
    (hMeta : st.lifecycle.objectTypes[target]? = some currentObj.objectType)
    (hNoAuth : lifecycleRetypeAuthority cap target = false) :
    lifecycleRetypeDirect cap target newObj st = .error .illegalAuthority := by
  unfold lifecycleRetypeDirect; simp [hSome, hMeta, hNoAuth]

-- ============================================================================
-- U-H04: lifecycleRetypeDirectWithCleanup — pre-resolved authority + safe path
-- ============================================================================

/-- U-H04: Safe lifecycle retype with pre-resolved authority capability.

Combines `lifecycleRetypeDirect`'s pre-resolved cap dispatch with the
cleanup and memory scrubbing guarantees of `lifecycleRetypeWithCleanup`.
This is the correct entry point for API dispatch, which resolves the
authority cap before entering the retype arm.

Phases:
1. Well-formedness validation (T5-D defense-in-depth)
2. `lifecyclePreRetypeCleanup` — TCB scheduler dequeue + CNode CDT detach
3. `scrubObjectMemory` — zero backing memory (S6-C security guarantee)
4. `lifecycleRetypeDirect` — replace object in store with authority check -/
def lifecycleRetypeDirectWithCleanup
    (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    -- T5-D: Validate new object well-formedness before proceeding
    if ¬ newObj.wellFormed st.objects then
      .error .illegalState
    else
      match st.objects[target]? with
      | none => lifecycleRetypeDirect authCap target newObj st
      | some currentObj =>
          let stClean := lifecyclePreRetypeCleanup st target currentObj newObj
          let stScrubbed := scrubObjectMemory stClean target currentObj.objectType
          lifecycleRetypeDirect authCap target newObj stScrubbed

end SeLe4n.Kernel
