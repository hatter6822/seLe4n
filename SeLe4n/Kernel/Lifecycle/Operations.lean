/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.IPC.Operations

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Lifecycle authority required to retype an object identity in this slice.

The authority capability must target the object directly and include `write` rights. -/
def lifecycleRetypeAuthority (cap : Capability) (target : SeLe4n.ObjId) : Bool :=
  decide (cap.target = .object target) && Capability.hasRight cap .write


-- ============================================================================
-- WS-H2: Lifecycle Safety Guards
-- ============================================================================

/-- WS-H2/H-05: Clean up external references to a TCB being retyped away.
    Removes the ThreadId from the scheduler run queue (`removeRunnable`).
    This prevents the dangling-reference scenario described in H-05: after a TCB
    is retyped, its ThreadId must not remain in the run queue pointing at what
    is now a different object type.

    Note: IPC endpoint queue references become stale after retype but are
    safe — all IPC operations guard on `lookupTcb`, which fails gracefully
    when the TCB no longer exists.  Full endpoint dequeue is deferred to a
    future workstream to avoid breaking the `objects`-preservation chain
    used by downstream invariant proofs. -/
def cleanupTcbReferences (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  removeRunnable st tid

/-- After cleanup, the cleaned thread is not in the run queue. -/
theorem cleanupTcbReferences_removes_from_runnable
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    ¬(tid ∈ (cleanupTcbReferences st tid).scheduler.runQueue) := by
  unfold cleanupTcbReferences removeRunnable
  exact RunQueue.not_mem_remove_self _ _

/-- Cleanup preserves run queue membership for other threads. -/
theorem cleanupTcbReferences_preserves_runnable_ne
    (st : SystemState) (tid other : SeLe4n.ThreadId) (hNe : other ≠ tid)
    (hMem : other ∈ st.scheduler.runQueue) :
    other ∈ (cleanupTcbReferences st tid).scheduler.runQueue := by
  unfold cleanupTcbReferences removeRunnable
  rw [RunQueue.mem_remove]
  exact ⟨hMem, hNe⟩

/-- Cleanup preserves the objects store (scheduler-only operation). -/
theorem cleanupTcbReferences_objects_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).objects = st.objects := by
  unfold cleanupTcbReferences removeRunnable; rfl

/-- Cleanup preserves lifecycle metadata (scheduler-only operation). -/
theorem cleanupTcbReferences_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).lifecycle = st.lifecycle := by
  unfold cleanupTcbReferences removeRunnable; rfl

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
  cn.slots.toList.foldl (fun acc pair =>
    SystemState.detachSlotFromCdt acc { cnode := cnodeId, slot := pair.1 }
  ) st

/-- `detachCNodeSlots` preserves the objects store (CDT-only operation). -/
theorem detachCNodeSlots_objects_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).objects = st.objects := by
  simp only [detachCNodeSlots]
  have key : ∀ (l : List (SeLe4n.Slot × Capability)) (acc : SystemState),
    (l.foldl (fun acc' pair =>
      SystemState.detachSlotFromCdt acc' { cnode := cnodeId, slot := pair.1 }) acc).objects
      = acc.objects := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons pair rest ih =>
      intro acc
      simp only [List.foldl]
      exact (ih _).trans (detachSlotFromCdt_objects_eq acc { cnode := cnodeId, slot := pair.1 })
  exact key cn.slots.toList st

/-- `detachCNodeSlots` preserves lifecycle metadata (CDT-only operation). -/
theorem detachCNodeSlots_lifecycle_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).lifecycle = st.lifecycle := by
  simp only [detachCNodeSlots]
  have key : ∀ (l : List (SeLe4n.Slot × Capability)) (acc : SystemState),
    (l.foldl (fun acc' pair =>
      SystemState.detachSlotFromCdt acc' { cnode := cnodeId, slot := pair.1 }) acc).lifecycle
      = acc.lifecycle := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons pair rest ih =>
      intro acc
      simp only [List.foldl]
      exact (ih _).trans (detachSlotFromCdt_lifecycle_eq acc { cnode := cnodeId, slot := pair.1 })
  exact key cn.slots.toList st

/-- WS-H2: Pre-retype cleanup combining TCB reference cleanup and CDT detach.
    - If the current object is a TCB: clean up scheduler references.
    - If the current object is a CNode being replaced by a non-CNode: detach
      CDT slot mappings to prevent orphaned derivation tree references. -/
def lifecyclePreRetypeCleanup (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) : SystemState :=
  let st := match currentObj with
    | .tcb tcb => cleanupTcbReferences st tcb.tid
    | _ => st
  match currentObj with
  | .cnode cn =>
    match newObj with
    | .cnode _ => st  -- CNode → CNode: no CDT cleanup needed
    | _ => detachCNodeSlots st target cn
  | _ => st

/-- Pre-retype cleanup preserves the objects store. -/
theorem lifecyclePreRetypeCleanup_objects_eq
    (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) :
    (lifecyclePreRetypeCleanup st target currentObj newObj).objects = st.objects := by
  unfold lifecyclePreRetypeCleanup
  cases currentObj with
  | tcb tcb => exact cleanupTcbReferences_objects_eq st tcb.tid
  | cnode cn =>
    cases newObj <;> simp only [] <;>
    first | rfl | exact detachCNodeSlots_objects_eq st target cn
  | endpoint _ | notification _ | vspaceRoot _ | untyped _ => rfl

/-- Pre-retype cleanup preserves lifecycle metadata. -/
theorem lifecyclePreRetypeCleanup_lifecycle_eq
    (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) :
    (lifecyclePreRetypeCleanup st target currentObj newObj).lifecycle = st.lifecycle := by
  unfold lifecyclePreRetypeCleanup
  cases currentObj with
  | tcb tcb => exact cleanupTcbReferences_lifecycle_eq st tcb.tid
  | cnode cn =>
    cases newObj <;> simp only [] <;>
    first | rfl | exact detachCNodeSlots_lifecycle_eq st target cn
  | endpoint _ | notification _ | vspaceRoot _ | untyped _ => rfl


/-- Pre-retype cleanup only removes elements from the flat list, never adds. -/
private theorem cleanupTcbReferences_flat_subset
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (h : x ∈ (cleanupTcbReferences st tid).scheduler.runQueue.flat) :
    x ∈ st.scheduler.runQueue.flat := by
  unfold cleanupTcbReferences removeRunnable at h
  simp only [] at h
  exact (List.mem_filter.mp h).1

/-- CDT cleanup preserves the scheduler. -/
private theorem detachCNodeSlots_scheduler_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).scheduler = st.scheduler := by
  simp only [detachCNodeSlots]
  have key : ∀ (l : List (SeLe4n.Slot × Capability)) (acc : SystemState),
    (l.foldl (fun acc' pair =>
      SystemState.detachSlotFromCdt acc' { cnode := cnodeId, slot := pair.1 }) acc).scheduler
      = acc.scheduler := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons pair rest ih =>
      intro acc
      simp only [List.foldl]
      have hDetach : (SystemState.detachSlotFromCdt acc { cnode := cnodeId, slot := pair.1 }).scheduler
          = acc.scheduler := by unfold SystemState.detachSlotFromCdt; split <;> rfl
      exact (ih _).trans hDetach
  exact key cn.slots.toList st

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
    exact cleanupTcbReferences_flat_subset st tcb.tid x h
  | cnode cn =>
    cases newObj <;> simp only [] at h
    all_goals first
      | exact h
      | (have hSched := detachCNodeSlots_scheduler_eq st target cn
         rw [show (detachCNodeSlots st target cn).scheduler.runQueue.flat =
               st.scheduler.runQueue.flat from by rw [hSched]] at h
         exact h)
  | endpoint _ | notification _ | vspaceRoot _ | untyped _ => exact h

/-- Retype an existing object id to a new typed object value.

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
- final retype failures are propagated directly. -/
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

/-- WS-F2: Retype a new typed object from an untyped memory region.

Deterministic branch contract:
1. The source object must exist and be an `UntypedObject` (`untypedTypeMismatch` otherwise).
2. Device untypeds cannot back typed kernel objects except other untypeds
   (`untypedDeviceRestriction` if violated).
3. The allocation size must be at least `objectTypeAllocSize` for the target type
   (`untypedAllocSizeTooSmall` otherwise).
4. Authority capability must target the untyped object and include `write` rights
   (`illegalAuthority` otherwise).
5. The requested allocation size must fit within the remaining region space
   (`untypedRegionExhausted` otherwise).
6. On success: watermark is advanced, new child is recorded, and the new typed
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
        -- WS-H2/H-06: childId must not equal untypedId (self-overwrite guard)
        if childId = untypedId then
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

/-- WS-F2: Decomposition of a successful `retypeFromUntyped` into constituent steps. -/
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
          cases hDevBool : ut.isDevice <;> simp only [hDevBool] at hStep
          · -- ut.isDevice = false: device check trivially passes
            simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hStep
            by_cases hAllocSz : allocSize < objectTypeAllocSize newObj.objectType
            · simp [hAllocSz] at hStep
            · simp [hAllocSz] at hStep
              cases hLookup : cspaceLookupSlot authority st with
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
                        cases hStoreUt : storeObject untypedId (.untyped ut') stLookup with
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
              · simp [hAllocSz] at hStep
                cases hLookup : cspaceLookupSlot authority st with
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
                          cases hStoreUt : storeObject untypedId (.untyped ut') stLookup with
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
    (hNeSelf : childId ≠ untypedId)
    (hNoCollision : st.objects[childId]?.isSome = false)
    (hFreshChildren : ut.children.any (fun c => c.objId == childId) = false)
    (hNotDev : ut.isDevice = false ∨ newObj.objectType = .untyped)
    (hSmall : allocSize < objectTypeAllocSize newObj.objectType) :
    retypeFromUntyped authority untypedId childId newObj allocSize st =
      .error .untypedAllocSizeTooSmall := by
  unfold retypeFromUntyped
  simp [hObj, hNeSelf, hNoCollision, hFreshChildren]
  cases hNotDev with
  | inl hFalse => simp [hFalse, hSmall]
  | inr hUt =>
      rw [hUt] at hSmall
      by_cases hDevBool : ut.isDevice
      · simp [hDevBool, hUt, hSmall]
      · simp [hDevBool, hUt, hSmall]

/-- WS-F2: `retypeFromUntyped` returns `untypedRegionExhausted` when allocation cannot fit. -/
theorem retypeFromUntyped_error_regionExhausted
    (st : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (newObj : KernelObject)
    (allocSize : Nat) (ut : UntypedObject) (cap : Capability)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hNeSelf : childId ≠ untypedId)
    (hNoCollision : st.objects[childId]?.isSome = false)
    (hFreshChildren : ut.children.any (fun c => c.objId == childId) = false)
    (hNotDev : ut.isDevice = false ∨ newObj.objectType = .untyped)
    (hAllocSzOk : ¬(allocSize < objectTypeAllocSize newObj.objectType))
    (hLookup : cspaceLookupSlot authority st = .ok (cap, st))
    (hAuth : lifecycleRetypeAuthority cap untypedId = true)
    (hNoFit : ut.allocate childId allocSize = none) :
    retypeFromUntyped authority untypedId childId newObj allocSize st =
      .error .untypedRegionExhausted := by
  unfold retypeFromUntyped
  simp [hObj, hNeSelf, hNoCollision, hFreshChildren]
  cases hNotDev with
  | inl hFalse => simp [hFalse, hAllocSzOk, hLookup, hAuth, hNoFit]
  | inr hUt =>
      rw [hUt] at hAllocSzOk
      by_cases hDevBool : ut.isDevice
      · simp [hDevBool, hUt, hAllocSzOk, hLookup, hAuth, hNoFit]
      · simp [hDevBool, hUt, hAllocSzOk, hLookup, hAuth, hNoFit]

/- Local lifecycle transition helper lemmas (M4-A step 4).
These theorems keep preservation scripts focused on invariant obligations rather than
repeating transition case analysis. -/

theorem lifecycle_storeObject_objects_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[id]? = some obj :=
  SeLe4n.Model.storeObject_objects_eq st st' id obj hStore

theorem lifecycle_storeObject_objects_ne
    (st st' : SystemState)
    (id oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hNe : oid ≠ id)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[oid]? = st.objects[oid]? :=
  SeLe4n.Model.storeObject_objects_ne st st' id oid obj hNe hStore

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
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    st'.objects[oid]? = st.objects[oid]? := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  exact lifecycle_storeObject_objects_ne st st' target oid newObj hNe hStore

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
  exact lifecycle_storeObject_objects_eq st st' target newObj hStore

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
-- WS-H2: Safe lifecycle retype wrapper (cleanup + retype)
-- ============================================================================

/-- WS-H2: Safe lifecycle retype with reference cleanup.
    Composes `lifecyclePreRetypeCleanup` (TCB scheduler dequeue + CNode CDT detach)
    with `lifecycleRetypeObject`.  The cleanup runs on the pre-retype state;
    the actual retype operates on the cleaned state.

    Since cleanup preserves `objects` and `lifecycle`, the retype authority check
    and lifecycle metadata check succeed on the cleaned state iff they succeed on
    the original state.

    This wrapper is the recommended entry point for callers that need the
    H-05 safety guarantee (`lifecycleRetypeWithCleanup_ok_runnable_no_dangling`). -/
def lifecycleRetypeWithCleanup
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match st.objects[target]? with
    | none => lifecycleRetypeObject authority target newObj st
    | some currentObj =>
        let stClean := lifecyclePreRetypeCleanup st target currentObj newObj
        lifecycleRetypeObject authority target newObj stClean

/-- WS-H2/H-05: After a TCB retype via the safe wrapper, the old ThreadId is
    not in the run queue.  This is the key safety property required by H-05. -/
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
  simp only [hObj] at hStep
  -- hStep now has lifecycleRetypeObject on the cleaned state
  rcases lifecycleRetypeObject_ok_as_storeObject _ st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  have hSchedEq : st'.scheduler =
      (lifecyclePreRetypeCleanup st target (.tcb tcb) newObj).scheduler :=
    lifecycle_storeObject_scheduler_eq _ st' target newObj hStore
  rw [hSchedEq]
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
      radixWidth := 0, slots := {}
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

/-- WS-K-D: `objectOfTypeTag` is pure. -/
theorem objectOfTypeTag_deterministic (tag : Nat) (size : Nat) :
    objectOfTypeTag tag size = objectOfTypeTag tag size := rfl

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

-- ============================================================================
-- WS-K-D: lifecycleRetypeDirect — pre-resolved authority variant
-- ============================================================================

/-- WS-K-D: Retype with a pre-resolved authority capability.
Companion to `lifecycleRetypeObject` for the register-sourced dispatch
path where the authority cap has already been resolved by `syscallInvoke`.

Deterministic branch contract:
1. Target object must exist (`objectNotFound` otherwise).
2. Lifecycle metadata must agree with object-store type (`illegalState`).
3. Authority cap must satisfy `lifecycleRetypeAuthority` — targets the
   object with `.write` right (`illegalAuthority` otherwise).
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

/-- WS-K-D: `lifecycleRetypeDirect` is pure. -/
theorem lifecycleRetypeDirect_deterministic
    (cap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject) :
    lifecycleRetypeDirect cap target newObj =
    lifecycleRetypeDirect cap target newObj := rfl

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

end SeLe4n.Kernel
