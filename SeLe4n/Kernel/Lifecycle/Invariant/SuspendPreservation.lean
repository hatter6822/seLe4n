/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Suspend

/-! # D1-I: Suspension & Resumption Preservation Theorems

Proves that `suspendThread` and `resumeThread` helper functions preserve
the kernel's scheduler and serviceRegistry fields.

## Proof structure

### Transport lemmas (D1-I)
Each helper function preserves non-object state fields:
- `cancelIpcBlocking` preserves scheduler, serviceRegistry, lifecycle
- `cancelDonation` preserves scheduler, serviceRegistry
- `clearPendingState` preserves scheduler, serviceRegistry, lifecycle

Note: `cancelDonation` does NOT preserve lifecycle in the `.donated` case
because `returnDonatedSchedContext` calls `storeObject`, which updates
`lifecycle.objectTypes` and `lifecycle.capabilityRefs`. The `cancelIpcBlocking`
and `clearPendingState` helpers DO preserve lifecycle because they only use
direct record-with updates on the `objects` field.
-/

namespace SeLe4n.Kernel.Lifecycle.Suspend

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- D1-I: Transport lemmas — scheduler field preservation
-- ============================================================================

/-- D1-I: cancelIpcBlocking only modifies `objects`, preserving the scheduler.
    Each IPC state branch either (a) is a no-op, (b) uses
    removeFromAllEndpointQueues (which preserves scheduler) then inserts into
    objects, or (c) uses removeFromAllNotificationWaitLists then inserts. -/
theorem cancelIpcBlocking_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    (cancelIpcBlocking st tid tcb).scheduler = st.scheduler := by
  unfold cancelIpcBlocking
  cases tcb.ipcState with
  | ready => rfl
  | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ =>
    -- clearTcbIpcFields preserves scheduler, removeFromAllEndpointQueues preserves scheduler
    rw [clearTcbIpcFields_scheduler_eq, removeFromAllEndpointQueues_scheduler_eq]
  | blockedOnReply _ _ =>
    rw [clearTcbIpcFields_scheduler_eq]
  | blockedOnNotification _ =>
    rw [clearTcbIpcFields_scheduler_eq, removeFromAllNotificationWaitLists_scheduler_eq]

/-- D1-I: cancelDonation only modifies `objects`, preserving the scheduler. -/
theorem cancelDonation_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    (cancelDonation st tid tcb).scheduler = st.scheduler := by
  unfold cancelDonation
  split
  · rfl
  · dsimp only []
    split <;> (split <;> rfl)
  · exact cleanupDonatedSchedContext_scheduler_eq st tid

/-- D1-I: clearPendingState only modifies `objects`, preserving the scheduler. -/
theorem clearPendingState_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearPendingState st tid).scheduler = st.scheduler := by
  unfold clearPendingState; split <;> rfl

-- ============================================================================
-- D1-I: Transport lemmas — serviceRegistry and lifecycle preservation
-- ============================================================================

/-- D1-I: cancelIpcBlocking preserves serviceRegistry. -/
theorem cancelIpcBlocking_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    (cancelIpcBlocking st tid tcb).serviceRegistry = st.serviceRegistry := by
  unfold cancelIpcBlocking
  cases tcb.ipcState with
  | ready => rfl
  | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ =>
    rw [clearTcbIpcFields_serviceRegistry_eq, removeFromAllEndpointQueues_serviceRegistry_eq]
  | blockedOnReply _ _ =>
    rw [clearTcbIpcFields_serviceRegistry_eq]
  | blockedOnNotification _ =>
    rw [clearTcbIpcFields_serviceRegistry_eq, removeFromAllNotificationWaitLists_serviceRegistry_eq]

/-- D1-I: clearPendingState preserves serviceRegistry. -/
theorem clearPendingState_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearPendingState st tid).serviceRegistry = st.serviceRegistry := by
  unfold clearPendingState; split <;> rfl

/-- D1-I: clearPendingState preserves lifecycle. -/
theorem clearPendingState_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearPendingState st tid).lifecycle = st.lifecycle := by
  unfold clearPendingState; split <;> rfl

/-- Helper: storeObject preserves serviceRegistry. -/
private theorem storeObject_serviceRegistry_eq (st : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (pair : Unit × SystemState)
    (h : storeObject oid obj st = .ok pair) :
    pair.2.serviceRegistry = st.serviceRegistry := by
  unfold storeObject at h; cases h; rfl

/-- Helper: returnDonatedSchedContext preserves serviceRegistry.
    Mirrors the proof structure of `returnDonatedSchedContext_scheduler_eq`. -/
private theorem returnDonatedSchedContext_serviceRegistry_eq
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    st'.serviceRegistry = st.serviceRegistry := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject scId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        cases hL1 : lookupTcb p1.2 originalOwner with
        | none => intro h; cases h
        | some _ =>
          simp only []
          cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only []
            cases hL2 : lookupTcb p2.2 serverTid with
            | none => intro h; cases h
            | some _ =>
              simp only []
              cases hS3 : storeObject serverTid.toObjId _ p2.2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only [Except.ok.injEq]
                intro hEq; subst hEq
                have h1 := storeObject_serviceRegistry_eq st _ _ _ hS1
                have h2 := storeObject_serviceRegistry_eq p1.2 _ _ _ hS2
                have h3 := storeObject_serviceRegistry_eq p2.2 _ _ _ hS3
                exact h3.trans (h2.trans h1)
    | _ => simp only []; intro h; cases h

/-- Helper: cleanupDonatedSchedContext preserves serviceRegistry. -/
private theorem cleanupDonatedSchedContext_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupDonatedSchedContext st tid).serviceRegistry = st.serviceRegistry := by
  unfold cleanupDonatedSchedContext
  cases lookupTcb st tid with
  | none => rfl
  | some tcb =>
    simp only []
    cases tcb.schedContextBinding with
    | unbound => rfl
    | bound _ => rfl
    | donated scId owner =>
      simp only []
      cases hReturn : returnDonatedSchedContext st tid scId owner with
      | error _ => rfl
      | ok st' => exact returnDonatedSchedContext_serviceRegistry_eq st st' tid scId owner hReturn

/-- D1-I: cancelDonation preserves serviceRegistry. -/
theorem cancelDonation_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    (cancelDonation st tid tcb).serviceRegistry = st.serviceRegistry := by
  unfold cancelDonation
  split
  · -- .unbound
    rfl
  · -- .bound scId: two nested matches, all branches preserve serviceRegistry
    -- The let-bound st1 is one of { st with objects := ... } or st itself.
    -- In either case st1.serviceRegistry = st.serviceRegistry.
    -- The final result is { st1 with objects := ... } or st1, both preserving serviceRegistry.
    dsimp only []
    split <;> (split <;> rfl)
  · -- .donated: delegate to cleanupDonatedSchedContext
    exact cleanupDonatedSchedContext_serviceRegistry_eq st tid

-- ============================================================================
-- D1-I: Transport lemmas — lifecycle preservation
-- ============================================================================

/-- D1-I: cancelIpcBlocking preserves lifecycle. -/
theorem cancelIpcBlocking_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    (cancelIpcBlocking st tid tcb).lifecycle = st.lifecycle := by
  unfold cancelIpcBlocking
  cases tcb.ipcState with
  | ready => rfl
  | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ =>
    rw [clearTcbIpcFields_lifecycle_eq, removeFromAllEndpointQueues_lifecycle_eq]
  | blockedOnReply _ _ =>
    rw [clearTcbIpcFields_lifecycle_eq]
  | blockedOnNotification _ =>
    rw [clearTcbIpcFields_lifecycle_eq, removeFromAllNotificationWaitLists_lifecycle_eq]

end SeLe4n.Kernel.Lifecycle.Suspend
