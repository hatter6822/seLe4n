-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.CleanupPreservation

/-!
AN4-G.5 (LIF-M05) child module extracted from
`SeLe4n.Kernel.Lifecycle.Operations`. Contains the untyped-memory model
(`objectTypeAllocSize`, `requiresPageAlignment`, `allocationBasePageAligned`),
the object-identifier address-space guard, the `retypeFromUntyped`
definition, and the complete preservation / soundness theorem cluster
that witnesses its capacity-gated, fresh-id-allocating, and
sequentially-atomic behaviour.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- WS-F2: Untyped Memory Model — retypeFromUntyped
-- ============================================================================

/-- WS-F2: The smallest allocation a kernel object type can be carved in — the
floor `retypeFromUntyped` holds every carve to (`untypedAllocSizeTooSmall`).

WS-ZA ZA5.4 part 14: the kernel kinds are seL4's AArch64 MCS object sizes
(`getObjectSize`, `libsel4/sel4_arch_include/aarch64/sel4/sel4_arch/constants.h`):
a thread `2 ^ seL4_TCBBits` (11), an endpoint `2 ^ seL4_EndpointBits` (4), a
notification `2 ^ seL4_NotificationBits` (6 under MCS), a reply
`2 ^ seL4_ReplyBits` (5), and for the two kinds whose size the caller names, the
least it may name: a CNode of one radix bit (`2 ^ (1 + seL4_SlotBits)`) and a
scheduling context of `2 ^ seL4_MinSchedContextBits` (7).  A carve's own size is
`CarveRequest.size`, which is never below these. -/
def objectTypeAllocSize : KernelObjectType → Nat
  | .tcb => 2 ^ 11
  | .endpoint => 2 ^ 4
  | .notification => 2 ^ 6
  | .cnode => 2 ^ (1 + 5)
  | .vspaceRoot => 4096
  | .untyped => 4096
  | .schedContext => 2 ^ 7
  | .reply => 2 ^ 5
  -- WS-BP BP7.1: a frame is one page of the memory it is carved from.
  | .frame => SeLe4n.pageBytes
  -- WS-BP BP7.1 (`v0.36.12`): so is a page table.
  | .pageTable => SeLe4n.pageBytes

/-- S5-G: Predicate for object types that require page-aligned allocation bases.
VSpace roots and CNodes back page-table structures on ARM64, and a frame is
itself a page a mapping names by address, so their backing memory must start on
a 4KB page boundary. This matches seL4's alignment
requirement for page-table objects (seL4_PageTableObject, seL4_VSpaceObject). -/
def requiresPageAlignment : KernelObjectType → Bool
  | .vspaceRoot => true
  -- WS-BP BP7.1: a frame is mapped by address, and a mapping names a page.
  | .frame => true
  -- WS-BP BP7.1 (`v0.36.12`): a table descriptor names a page.
  | .pageTable => true
  -- WS-BP BP7.1 slice 4 (`v0.36.8`): a carved untyped starts on a page, so
  -- every frame carved from it can too — the carve's size is a multiple of a
  -- page (`minUntypedSizeBits`), which keeps the parent's next base aligned.
  | .untyped => true
  | _ => false

/-- WS-ZA ZA5.4 part 14: **the kinds aligned to their own size**, as seL4's
`Untyped_Retype` places every object at a multiple of its size
(`alignUp(freeRef, objectSize)` in `decodeUntypedInvocation`): the kernel
objects — a thread, an endpoint, a notification, a reply, a CNode and a
scheduling context.  A CNode is aligned to its size and not to a page, as in
seL4, so a CNode of one radix bit is 64 bytes on a 64-byte boundary.

The carve is at the invoked capability's free index, as for every kind, so a
base that is not a multiple of the object's size is refused
(`allocationMisaligned`) where seL4 would skip up to the next multiple. -/
def requiresSizeAlignment : KernelObjectType → Bool
  | .tcb => true
  | .endpoint => true
  | .notification => true
  | .cnode => true
  | .schedContext => true
  | .reply => true
  | .vspaceRoot => false
  | .untyped => false
  | .frame => false
  | .pageTable => false

/-- S5-G: Check whether the untyped allocation base at free index `idx`
(`regionBase + idx`) is page-aligned. Returns `true` when alignment is satisfied.
The index is the invoked capability's (`Capability.freeIndex`, seL4's
`capFreeIndex`), not the object's. -/
def allocationBasePageAligned (ut : UntypedObject) (idx : Nat) : Bool :=
  (ut.regionBase.toNat + idx) % 4096 == 0

/-- WS-ZA ZA5.4 part 14: **is the base at free index `idx` aligned as a carve of
`size` bytes of kind `ty` must be?**  On a page for the page kinds
(`requiresPageAlignment`), on a multiple of its own size for the kernel kinds
(`requiresSizeAlignment`), and anywhere otherwise.  The one alignment question
the carve asks before it writes. -/
def carveBaseAligned (ty : KernelObjectType) (size : Nat) (ut : UntypedObject) (idx : Nat) :
    Bool :=
  if requiresPageAlignment ty then allocationBasePageAligned ut idx
  else if requiresSizeAlignment ty then (ut.regionBase.toNat + idx) % size == 0
  else true

/-- A page kind's carve base is aligned exactly when it is on a page. -/
theorem carveBaseAligned_of_page {ty : KernelObjectType} (h : requiresPageAlignment ty = true)
    (size : Nat) (ut : UntypedObject) (idx : Nat) :
    carveBaseAligned ty size ut idx = allocationBasePageAligned ut idx := by
  simp [carveBaseAligned, h]

-- ============================================================================
-- The object identifier's extent stays inside the physical address space
-- ============================================================================

/-- The largest extent any object kind has: a page. -/
def maxObjectAllocSize : Nat := SeLe4n.pageBytes

theorem objectTypeAllocSize_le_max (ty : KernelObjectType) :
    objectTypeAllocSize ty ≤ maxObjectAllocSize := by
  cases ty <;> simp [objectTypeAllocSize, maxObjectAllocSize, SeLe4n.pageBytes]

/-- Whether every extent `[childId × size, + size)` an identifier names (`size`
the `objectTypeAllocSize` of any kind) lies inside the machine's physical
address space: `(childId + 1) × maxObjectAllocSize ≤ 2 ^ width`,
compared as `childId < 2 ^ width / maxObjectAllocSize` so a refused identifier
is never multiplied out.  An object is memory, so its extent is a physical
range; an extent past the address width names no memory. -/
def objectIdInAddressSpace (ms : MachineState) (childId : SeLe4n.ObjId) : Bool :=
  childId.toNat < 2 ^ ms.physicalAddressWidth / maxObjectAllocSize

theorem objectIdInAddressSpace_extent (ms : MachineState) (childId : SeLe4n.ObjId)
    (h : objectIdInAddressSpace ms childId = true) (ty : KernelObjectType) :
    childId.toNat * objectTypeAllocSize ty + objectTypeAllocSize ty ≤
      2 ^ ms.physicalAddressWidth := by
  have hPos : 0 < maxObjectAllocSize := by simp [maxObjectAllocSize, SeLe4n.pageBytes]
  have hLt : childId.toNat < 2 ^ ms.physicalAddressWidth / maxObjectAllocSize := by
    simpa [objectIdInAddressSpace] using h
  have hLe : (childId.toNat + 1) * maxObjectAllocSize ≤ 2 ^ ms.physicalAddressWidth :=
    (Nat.le_div_iff_mul_le hPos).mp hLt
  have hTy : (childId.toNat + 1) * objectTypeAllocSize ty ≤ 2 ^ ms.physicalAddressWidth :=
    Nat.le_trans (Nat.mul_le_mul_left _ (objectTypeAllocSize_le_max ty)) hLe
  rw [Nat.succ_mul] at hTy
  exact hTy

/-- WS-F2: Retype a new typed object from an untyped memory region.

Deterministic branch contract:
1. The source object must exist and be an `UntypedObject` (`untypedTypeMismatch` otherwise).
2. A device untyped backs only the kinds `KernelObjectType.deviceBackable`
   admits — other untypeds and frames; never a translation table, since a table
   walk reading a device reads a register (`untypedDeviceRestriction` if
   violated).
3. The child's identifier must keep every extent it can name (at the largest
   kind) inside the machine's physical address space
   (`objectIdInAddressSpace`; `addressOutOfBounds` otherwise).
4. The allocation size must be at least `objectTypeAllocSize` for the target type
   (`untypedAllocSizeTooSmall` otherwise).
5. The authority slot must hold a capability (`cspaceLookupSlot`); its free
   index (`Capability.freeIndex`, seL4's `capFreeIndex`) is where the carve is
   made.
6. S5-G: For the kinds `requiresPageAlignment` names — VSpace roots,
   frames, page tables and child untypeds — the allocation base address
   (`regionBase + freeIndex`) must be page-aligned (4KB boundary); for the
   kernel kinds (`requiresSizeAlignment`) it must be a multiple of the
   allocation's own size, as seL4 places every object (`carveBaseAligned`).
   Returns `allocationMisaligned` if violated.
7. Authority capability must target the untyped object and include the `retype`
   right (`lifecycleRetypeAuthority`; `illegalAuthority` otherwise).
8. The requested allocation size must fit between the free index and the end of
   the region (`untypedRegionExhausted` otherwise).
9. U-H02: Post-allocation alignment re-verification — after advancing the index,
   the new base must still be page-aligned for VSpace-bound objects
   (`allocationMisaligned` otherwise). This prevents non-page-aligned allocations
   from shifting subsequent allocations to unaligned bases.
10. On success: the new child is recorded in the untyped, the new typed object is
   stored at `childId` via `storeObject`, and the authority capability's free
   index is advanced past the child in its slot (`setCapFreeIndex`), as seL4's
   `invokeUntyped_Retype` writes `capFreeIndex`. -/
def retypeFromUntyped
    (authority : CSpaceAddr)
    (untypedId : SeLe4n.ObjId)
    (childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat) : Kernel Unit :=
  fun st =>
    match st.getObject? untypedId with
    | none => .error .objectNotFound
    | some (.untyped ut) =>
        -- S4-B: Capacity check — reject allocation when object store is at capacity
        if st.objectIndex.length ≥ maxObjects then
          .error .objectStoreCapacityExceeded
        -- WS-H2/H-06: childId must not equal untypedId (self-overwrite guard)
        else if childId = untypedId then
          .error .childIdSelfOverwrite
        -- WS-H2/A-26: childId must not collide with an existing object
        else if (st.getObject? childId).isSome then
          .error .childIdCollision
        -- WS-H2/A-27: childId must not collide with an existing untyped child
        else if ut.children.any (fun c => c.objId == childId) then
          .error .childIdCollision
        -- Device untypeds cannot back typed kernel objects (except other untypeds)
        -- WS-BP BP7.1 (`v0.36.5`): a device untyped backs exactly a child
        -- untyped and a **frame**, which is how a driver is handed MMIO — and
        -- nothing the kernel itself reads.  This is seL4's rule
        -- (`Untyped_Retype` on a device untyped yields frames and untypeds
        -- only); it read `!= .untyped` while no frame existed, and
        -- `!memoryBacked` until `v0.36.9` made a VSpace root memory-backed — a
        -- table is memory, and must be RAM (`deviceBackable`).
        else if ut.isDevice && !newObj.objectType.deviceBackable then
          .error .untypedDeviceRestriction
        -- Every extent the child can hold must be physical memory (`objectIdInAddressSpace`)
        else if !objectIdInAddressSpace st.machine childId then
          .error .addressOutOfBounds
        -- Allocation size must be at least the minimum for the target object type
        else if allocSize < objectTypeAllocSize newObj.objectType then
          .error .untypedAllocSizeTooSmall
        else
          match cspaceLookupSlot authority st with
          | .error e => .error e
          | .ok (authCap, st') =>
            -- WS-ZA ZA5.4 part 13: the carve is at the invoked capability's free
            -- index (seL4's `capFreeIndex`), not at a word of the object.
            let idx := authCap.freeIndex
            -- S5-G: Page-alignment check for VSpace-bound objects; WS-ZA
            -- ZA5.4 part 14: a kernel object on a multiple of its own size.
            if !carveBaseAligned newObj.objectType allocSize ut idx then
              .error .allocationMisaligned
            else if lifecycleRetypeAuthority authCap untypedId then
                -- WS-H2/A-28: Both objects are computed before any state mutation.
                -- `ut'` and `newObj` are fully determined at this point.
                match ut.allocate idx childId allocSize with
                | none => .error .untypedRegionExhausted
                | some (ut', _offset) =>
                    -- U-H02: Post-allocation alignment re-verification.
                    -- After advancing the index by `allocSize`, the new base
                    -- (`regionBase + idx + allocSize`) must remain page-aligned if the
                    -- object type requires it. Non-page-aligned allocations would
                    -- shift subsequent allocations to unaligned bases, violating S5-G.
                    if requiresPageAlignment newObj.objectType &&
                        !allocationBasePageAligned ut (idx + allocSize) then
                      .error .allocationMisaligned
                    else
                    -- Atomic store: the child recorded in the untyped, the child
                    -- created, and the invoked capability's free index advanced.
                    -- AN6-C.2 (H-09): Per-caller contract — callers allocating a
                    -- `.untyped` child via this primitive SHOULD pre-stamp the
                    -- child's `parent` field with the parent untyped's ObjId
                    -- before invocation so the transitive
                    -- `untypedAncestorRegionsDisjoint` invariant (AN6-C.4) can
                    -- walk the ancestor chain.  The one live caller carving an
                    -- `.untyped` child, the untyped carve (`untypedRetypeObject`),
                    -- honours it: its child is `untypedNextChild`, which sets
                    -- `parent := some untypedId` and the carved region.
                    match storeObject untypedId (.untyped ut') st' with
                    | .error e => .error e
                    | .ok ((), stUt) =>
                        match storeObject childId newObj stUt with
                        | .error e => .error e
                        | .ok ((), stCh) => .ok ((), setCapFreeIndex stCh authority (idx + allocSize))
            else
                .error .illegalAuthority
    | some _ => .error .untypedTypeMismatch

/-- AF2-A2: The `storeObject` call that creates a new object in
    `retypeFromUntyped` (line 668) is gated by the capacity check at line 626.
    If `retypeFromUntyped` succeeds, then `st.objectIndex.length < maxObjects`
    held at entry. This is the allocation-boundary half of the capacity safety
    proof; the in-place-mutation half is `storeObject_capacity_safe_of_existing`
    (Model/State.lean). -/
theorem retypeFromUntyped_capacity_gated
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (st st' : SystemState)
    (hOk : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    st.objectIndex.length < maxObjects := by
  unfold retypeFromUntyped SystemState.getObject? at hOk
  cases h1 : st.objects[untypedId]? with
  | none => simp [h1] at hOk
  | some obj =>
    simp [h1] at hOk
    cases obj with
    | untyped ut =>
      simp at hOk
      split at hOk
      · simp at hOk
      · rename_i hLt; exact Nat.lt_of_not_le hLt
    | tcb _ | endpoint _ | notification _ | cnode _ | vspaceRoot _ | schedContext _ | reply _ | frame _ | pageTable _ =>
      simp at hOk

/-- AJ2-D (M-09): Allocation freshness — if `retypeFromUntyped` succeeds, the
    `childId` was NOT in the object store before allocation. This is the formal
    foundation for typed ID namespace disjointness: since every new object
    (`.tcb`, `.schedContext`, etc.) is created at a previously-empty ObjId,
    two different typed IDs (e.g., `ThreadId(5)` and `SchedContextId(5)`) cannot
    simultaneously reference valid objects — the object store maps each ObjId
    to exactly one `KernelObject` variant by construction.

    The guard at line 664 (`st.objects[childId]?.isSome`) rejects allocation
    when the ObjId is already occupied, ensuring all new allocations are fresh. -/
theorem retypeFromUntyped_childId_fresh
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (st st' : SystemState)
    (hOk : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    st.objects[childId]?.isSome = false := by
  unfold retypeFromUntyped SystemState.getObject? at hOk
  cases h1 : st.objects[untypedId]? with
  | none => simp [h1] at hOk
  | some obj =>
    simp [h1] at hOk
    cases obj with
    | untyped ut =>
      simp at hOk
      split at hOk
      · simp at hOk
      · split at hOk
        · simp at hOk
        · -- childId collision guard
          cases hColl : st.objects[childId]?.isSome
          · rfl
          · simp [hColl] at hOk
    | tcb _ | endpoint _ | notification _ | cnode _ | vspaceRoot _ | schedContext _ | reply _ | frame _ | pageTable _ =>
      simp at hOk

/-- WS-F2: Decomposition of a successful `retypeFromUntyped` into constituent steps.
S5-G: The alignment check is an additional error guard (returns `allocationMisaligned`
for VSpace/CNode objects on unaligned bases); it does not affect the decomposition
since success implies the guard passed.  WS-ZA ZA5.4 part 13: the carve is at the
authority capability's free index, and its last step advances that index in the
authority's slot. -/
theorem retypeFromUntyped_ok_decompose
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    ∃ ut ut' cap stLookup stUt offset stCh,
      st.objects[untypedId]? = some (.untyped ut) ∧
      (ut.isDevice = false ∨ newObj.objectType.deviceBackable = true) ∧
      ¬(allocSize < objectTypeAllocSize newObj.objectType) ∧
      cspaceLookupSlot authority st = .ok (cap, stLookup) ∧
      lifecycleRetypeAuthority cap untypedId = true ∧
      ut.allocate cap.freeIndex childId allocSize = some (ut', offset) ∧
      storeObject untypedId (.untyped ut') stLookup = .ok ((), stUt) ∧
      storeObject childId newObj stUt = .ok ((), stCh) ∧
      st' = setCapFreeIndex stCh authority (cap.freeIndex + allocSize) := by
  unfold retypeFromUntyped SystemState.getObject? at hStep
  cases hObj : st.objects[untypedId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj
    all_goals simp only [hObj] at hStep
    case untyped ut =>
      split at hStep
      · cases hStep
      split at hStep
      · cases hStep
      split at hStep
      · cases hStep
      split at hStep
      · cases hStep
      split at hStep
      · cases hStep
      next hDev =>
      split at hStep
      · cases hStep
      split at hStep
      · cases hStep
      next hSz =>
      cases hLookup : cspaceLookupSlot authority st with
      | error e => simp only [hLookup] at hStep; cases hStep
      | ok pair =>
        obtain ⟨cap, stLookup⟩ := pair
        simp only [hLookup] at hStep
        split at hStep
        · cases hStep
        split at hStep
        · next hAuth =>
          cases hAlloc : ut.allocate cap.freeIndex childId allocSize with
          | none => simp only [hAlloc] at hStep; cases hStep
          | some r =>
            obtain ⟨ut', offset⟩ := r
            simp only [hAlloc] at hStep
            split at hStep
            · cases hStep
            cases hU : storeObject untypedId (.untyped ut') stLookup with
            | error e => simp only [hU] at hStep; cases hStep
            | ok p2 =>
              obtain ⟨⟨⟩, stUt⟩ := p2
              simp only [hU] at hStep
              cases hC : storeObject childId newObj stUt with
              | error e => simp only [hC] at hStep; cases hStep
              | ok p3 =>
                obtain ⟨⟨⟩, stCh⟩ := p3
                simp only [hC, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                refine ⟨ut, ut', cap, stLookup, stUt, offset, stCh, rfl, ?_, hSz, rfl, hAuth,
                  hAlloc, hU, hC, hStep.symm⟩
                revert hDev
                cases ut.isDevice <;> cases newObj.objectType.deviceBackable <;> simp
        · cases hStep
    all_goals cases hStep

/-- AN4-G.4 (LIF-M04): **retype atomicity under sequential semantics.**
The `retypeFromUntyped` primitive performs three mutations back-to-back: the
child's record in the parent (`storeObject untypedId (.untyped ut')`), the
fresh-object store (`storeObject childId newObj`) that materialises the child,
and the advance of the authority capability's free index
(`setCapFreeIndex`). In Lean's deterministic evaluation, these steps
collapse into a single indivisible transition from caller's perspective — there
is no observable intermediate state between them, so the three stores are
atomic at the model layer.

This witness discharges the "retype atomicity" obligation at the
sequential semantic level. On real hardware (SMP / preemption-capable
AArch64) the same atomicity must be re-established by a critical section
around `retypeFromUntyped`; the obligation is tracked for AN9-D (HAL
bracket) and AN12-B (SMP inventory confirmation — recorded as a post-1.0
hardening candidate; registered in `docs/REGISTERED_DEBT.md`
(Registered debt index, C.1)). -/
theorem retypeFromUntyped_atomicity_under_sequential_semantics
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    -- Atomicity witness: between the pre-state `st` and the post-state
    -- `st'`, there is exactly one observable transition — even though the
    -- implementation performs the record, the child store and the index
    -- advance as three sequential stores. The intermediate state `stUt` is
    -- existentially bound and never visible to the caller. The
    -- `storeObject childId newObj stUt = .ok ((), st')` conjunct witnesses
    -- that `stUt → st'` is the final child-store step; the fact that
    -- `stUt` is reachable from `st` via the record is recorded
    -- by the decomposition theorem invoked internally. -/
    ∃ stUt stCh idx, storeObject childId newObj stUt = .ok ((), stCh) ∧
      st' = setCapFreeIndex stCh authority idx := by
  obtain ⟨_, _, _, _, stUt, _, stCh, _, _, _, _, _, _, _, hStoreChild, hIdx⟩ :=
    retypeFromUntyped_ok_decompose st st' authority untypedId childId newObj allocSize hStep
  exact ⟨stUt, stCh, _, hStoreChild, hIdx⟩

/-- WS-F2: `retypeFromUntyped` returns `untypedTypeMismatch` when the source is not an untyped. -/
theorem retypeFromUntyped_error_typeMismatch
    (st : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (newObj : KernelObject)
    (allocSize : Nat) (obj : KernelObject)
    (hObj : st.objects[untypedId]? = some obj)
    (hNotUntyped : ∀ u, obj ≠ .untyped u) :
    retypeFromUntyped authority untypedId childId newObj allocSize st = .error .untypedTypeMismatch := by
  unfold retypeFromUntyped SystemState.getObject?
  cases obj with
  | untyped u => exact absurd rfl (hNotUntyped u)
  | tcb _ => simp [hObj]
  | endpoint _ => simp [hObj]
  | notification _ => simp [hObj]
  | cnode _ => simp [hObj]
  | vspaceRoot _ => simp [hObj]
  | schedContext _ => simp [hObj]
  | reply _ | frame _ | pageTable _ => simp [hObj]


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
    (hNotDev : ut.isDevice = false ∨ newObj.objectType.deviceBackable = true)
    (hExt : objectIdInAddressSpace st.machine childId = true)
    (hSmall : allocSize < objectTypeAllocSize newObj.objectType) :
    retypeFromUntyped authority untypedId childId newObj allocSize st =
      .error .untypedAllocSizeTooSmall := by
  unfold retypeFromUntyped SystemState.getObject?
  have hCapF : ¬(st.objectIndex.length ≥ maxObjects) := by omega
  simp [hObj, hCapF, hNeSelf, hNoCollision, hFreshChildren]
  cases hNotDev with
  | inl hFalse => simp [hFalse, hExt, hSmall]
  | inr hMB =>
      by_cases hDevBool : ut.isDevice
      · simp [hDevBool, hMB, hExt, hSmall]
      · simp [hDevBool, hExt, hSmall]

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
    (hNotDev : ut.isDevice = false ∨ newObj.objectType.deviceBackable = true)
    (hExt : objectIdInAddressSpace st.machine childId = true)
    (hAllocSzOk : ¬(allocSize < objectTypeAllocSize newObj.objectType))
    (hLookup : cspaceLookupSlot authority st = .ok (cap, st))
    (hAlignOk : carveBaseAligned newObj.objectType allocSize ut cap.freeIndex = true)
    (hAuth : lifecycleRetypeAuthority cap untypedId = true)
    (hNoFit : ut.allocate cap.freeIndex childId allocSize = none) :
    retypeFromUntyped authority untypedId childId newObj allocSize st =
      .error .untypedRegionExhausted := by
  unfold retypeFromUntyped SystemState.getObject?
  have hCapF : ¬(st.objectIndex.length ≥ maxObjects) := by omega
  simp only [hObj, hCapF, ↓reduceIte, hNeSelf, hNoCollision, hFreshChildren]
  cases hNotDev with
  | inl hFalse =>
      simp only [hFalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hExt, Bool.not_true,
        hAllocSzOk, hAlignOk, ↓reduceIte, hLookup, hAuth, hNoFit]
  | inr hMB =>
      by_cases hDevBool : ut.isDevice
      · simp only [hDevBool, hMB, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
          hExt, hAllocSzOk, hAlignOk, ↓reduceIte, hLookup, hAuth, hNoFit]
      · simp only [hDevBool, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          hExt, Bool.not_true, hAllocSzOk, hAlignOk, ↓reduceIte, hLookup, hAuth, hNoFit]

/- Local lifecycle transition helper lemmas (M4-A step 4).
These theorems keep preservation scripts focused on invariant obligations rather than
repeating transition case analysis. -/

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
      -- AN10-residual (R1): destructure on the typed helper.
      cases hCN : st.getCNode? addr.cnode with
      | none => simp [hCap, hCN] at hLookup
      | some _ => simp [hCap, hCN] at hLookup
  | some cap' =>
      simp [hCap] at hLookup
      exact hLookup.2.symm




/-- WS-ZA ZA5.4 part 13: **a successful `retypeFromUntyped` as three stores**
from the state it was handed — the untyped's record, the child, and the
authority's CNode with the capability holding its advanced free index — for the
proofs that carry an invariant store by store.  The authority's CNode is the one
the lookup read, untouched by the first two stores (an untyped and a fresh id
are not it). -/
theorem retypeFromUntyped_ok_stores
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hObjInv : st.objects.invExt)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    ∃ ut ut' cap stUt offset stCh cn,
      st.objects[untypedId]? = some (.untyped ut) ∧
      (ut.isDevice = false ∨ newObj.objectType.deviceBackable = true) ∧
      ¬(allocSize < objectTypeAllocSize newObj.objectType) ∧
      cspaceLookupSlot authority st = .ok (cap, st) ∧
      lifecycleRetypeAuthority cap untypedId = true ∧
      ut.allocate cap.freeIndex childId allocSize = some (ut', offset) ∧
      st.objects[authority.cnode]? = some (.cnode cn) ∧
      cn.lookup authority.slot = some cap ∧
      authority.cnode ≠ untypedId ∧ authority.cnode ≠ childId ∧
      storeObject untypedId (.untyped ut') st = .ok ((), stUt) ∧
      storeObject childId newObj stUt = .ok ((), stCh) ∧
      stCh.objects[authority.cnode]? = some (.cnode cn) ∧
      storeObject authority.cnode
        (.cnode (cn.insert authority.slot (cap.withFreeIndex (cap.freeIndex + allocSize)))) stCh
        = .ok ((), st') := by
  have hFresh := retypeFromUntyped_childId_fresh authority untypedId childId newObj allocSize
    st st' hStep
  obtain ⟨ut, ut', cap, stL, stUt, offset, stCh, hObj, hDev, hSz, hLk, hAuth, hAlloc, hU, hC,
    rfl⟩ := retypeFromUntyped_ok_decompose st st' authority untypedId childId newObj allocSize hStep
  have hStL : stL = st := cspaceLookupSlot_ok_state_eq st authority cap stL hLk
  subst hStL
  have hL : SystemState.lookupSlotCap stL authority = some cap := by
    unfold cspaceLookupSlot at hLk
    cases hq : SystemState.lookupSlotCap stL authority with
    | none => rw [hq] at hLk; exfalso; revert hLk; dsimp only; split <;> simp
    | some c =>
      rw [hq] at hLk
      simp only [Except.ok.injEq, Prod.mk.injEq] at hLk
      rw [hLk.1]
  unfold SystemState.lookupSlotCap SystemState.lookupCNode at hL
  cases hO : stL.objects[authority.cnode]? with
  | none => rw [hO] at hL; cases hL
  | some o =>
    rw [hO] at hL
    cases o with
    | cnode cn =>
      have hNeU : authority.cnode ≠ untypedId := by
        intro h; rw [h, hObj] at hO; cases hO
      have hNeC : authority.cnode ≠ childId := by
        intro h; rw [← h, hO] at hFresh; cases hFresh
      have hInvU := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hU
      have hOCh : stCh.objects[authority.cnode]? = some (.cnode cn) := by
        rw [storeObject_objects_ne _ _ _ _ _ hNeC hInvU hC,
          storeObject_objects_ne _ _ _ _ _ hNeU hObjInv hU, hO]
      refine ⟨ut, ut', cap, stUt, offset, stCh, cn, hObj, hDev, hSz, hLk, hAuth, hAlloc, rfl, hL,
        hNeU, hNeC, hU, hC, hOCh, ?_⟩
      rw [← CNode.setFreeIndex_of_lookup hL]
      exact setCapFreeIndex_eq_storeObject hOCh
    | _ => cases hL

-- ============================================================================
-- WS-BP BP7.1 (`v0.36.5`): the untyped carve that mints frames
-- ============================================================================

/-- **WS-BP BP7.1: the frame an untyped's next page would be.**

The page at free index `idx` — `regionBase + idx`, the invoked capability's
index (`Capability.freeIndex`) — carrying the untyped's own device flag.  One definition, read by the carve that
creates the frame and by every statement about which memory it names, so the
two cannot describe different pages.  seL4's `Untyped_Retype` places a frame at
the untyped's free pointer the same way; a device untyped yields a device frame,
which is how a driver is handed MMIO.  Inlined, so a caller that reads only the
page's base or kind builds no frame record (WS-ZA ZA5.4). -/
@[inline] def untypedNextFrame (ut : UntypedObject) (idx : Nat) : FrameObject :=
  { base := SeLe4n.PAddr.ofNat (ut.regionBase.toNat + idx)
    isDevice := ut.isDevice }

/-- **WS-BP BP7.1: the capability a carve hands back for a frame.**  Read,
write and grant — the rights a frame capability's holder can exercise (map
readable, map writable, hand the frame on).  `.retype` is absent because a
frame is not retyped; its memory returns to its untyped (`untypedReset`). -/
def frameCapability (frameId : SeLe4n.ObjId) : Capability :=
  { target := .object frameId
    rights := AccessRightSet.ofList [.read, .write, .grant] }

/-- **WS-BP BP7.1: the memory write a carve performs.**  A RAM frame's page is
zeroed before any capability to it exists, so the memory a thread is handed
reveals nothing that was there before — firmware scratch, boot data, a previous
owner.  A **device** frame is not touched: its page is MMIO, where a store is a
command to a device rather than a scrub. -/
def carveZeroFrame (st : SystemState) (frame : FrameObject) : SystemState :=
  if frame.isDevice then st
  else { st with
          machine := SeLe4n.zeroMemoryRange st.machine frame.base SeLe4n.pageBytes
          -- WS-BP BP7.2: the same scrub, owed to physical memory.
          physicalWrites := st.physicalWrites.pushAfter st.physicalWritesDrained
            (SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage frame.base)
          physicalWritesDrained := false }

/-- **WS-BP BP7.1 slice 4 (`v0.36.8`): the size bounds of a carved untyped**, as
a power of two.  The lower bound is one page: every carve's base must stay on a
page boundary (`requiresPageAlignment .untyped`), so a child smaller than a page
would leave its parent's next carve misaligned — and the primitive's own
`objectTypeAllocSize .untyped` minimum is that page.  The upper bound is seL4's
`seL4_MaxUntypedBits` on AArch64 (`47`), which no physical region on the first
hardware target approaches; above it the size is not a region any carve could
satisfy, and a caller asking for one is refused at the decode rather than by the
region check. -/
def minUntypedSizeBits : Nat := 12
def maxUntypedSizeBits : Nat := 47

/-- **WS-BP BP7.1 slice 4 (`v0.36.8`): the child untyped a carve of `2 ^ sizeBits`
bytes would be.**

The region at free index `idx` — `[regionBase + idx,
regionBase + idx + 2 ^ sizeBits)` — of the parent's memory kind, with its
**parent stamped** (`parent := some parentId`) and nothing carved from it yet.
The stamp is what `retypeFromUntyped`'s AN6-C.2 contract asks every caller
carving an `.untyped` child to perform, and what the transitive
`untypedAncestorRegionsDisjoint` walk reads.  The carve is the only way a
live state acquires a child untyped, so this is the only child untyped a live
state can hold.  One definition, read by the carve and by every statement
about which memory the child owns. -/
def untypedNextChild (ut : UntypedObject) (idx : Nat) (parentId : SeLe4n.ObjId)
    (sizeBits : Nat) : UntypedObject :=
  { regionBase := SeLe4n.PAddr.ofNat (ut.regionBase.toNat + idx)
    regionSize := 2 ^ sizeBits
    isDevice := ut.isDevice
    parent := some parentId }

/-- **WS-BP BP7.1 slice 4: the capability a carve hands back for a child
untyped.**  Read, write and retype — the rights the boot hands the root task for
its own untypeds (`rpi5RootTaskUntypeds`), so a carved untyped is exactly as
usable as a boot one: `.retype` is the authority `lifecycleRetypeAuthority` asks
for, and it is what lets the holder carve from the child and reset it. -/
def untypedCapability (untypedId : SeLe4n.ObjId) : Capability :=
  { target := .object untypedId
    rights := AccessRightSet.ofList [.read, .write, .retype] }

/-- **WS-ZA ZA5.4 part 14: the capability a carve hands back for a kernel
object** — seL4's `seL4_AllRights` (read, write, grant and grant-reply), the
rights `createNewObjects` gives every capability it makes.  `.retype` is not a
right in seL4 and here authorises only an invocation of an untyped, so a kernel
object's capability does not carry it. -/
def kernelObjectRights : AccessRightSet := AccessRightSet.ofList [.read, .write, .grant, .grantReply]

/-- The capability a carve hands back for a kernel object it made: the object,
with `kernelObjectRights`. -/
def kernelObjectCapability (childId : SeLe4n.ObjId) : Capability :=
  { target := .object childId, rights := kernelObjectRights }

/-- seL4's AArch64 CNode slot size, `seL4_SlotBits`: a CNode of `r` radix bits is
`2 ^ (r + cnodeSlotBits)` bytes. -/
def cnodeSlotBits : Nat := 5

/-- The CNode radix a carve accepts: at least one bit (seL4 refuses a
zero-size CNode), and small enough that the CNode is no larger than the largest
untyped (`maxUntypedSizeBits`). -/
def minCNodeRadixBits : Nat := 1
def maxCNodeRadixBits : Nat := maxUntypedSizeBits - cnodeSlotBits

/-- The scheduling-context sizes a carve accepts, as powers of two: from seL4's
`seL4_MinSchedContextBits` (7) to the largest untyped. -/
def minSchedContextSizeBits : Nat := 7

/-- **WS-ZA ZA5.4 part 14: the thread a carve makes** — seL4's `createObject`
for `seL4_TCBObject`: inactive, at priority 0 with maximum controlled priority 0,
in the creating core's current domain (`ksCurDomain`) and with the creating
core as its affinity (`getCurrentCPUIndex`), no fault handler, no bound
notification, no scheduling context, and both space slots empty
(`tcbCTable` and `tcbVTable` hold null capabilities).  Its identity is the id it
is stored at. -/
def carvedTcb (childId : SeLe4n.ObjId) (domain : SeLe4n.DomainId)
    (core : SeLe4n.Kernel.Concurrency.CoreId) : TCB :=
  { tid := SeLe4n.ThreadId.ofObjId childId
    priority := SeLe4n.Priority.ofNat 0
    maxControlledPriority := SeLe4n.Priority.ofNat 0
    domain := domain
    cpuAffinity := some core
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

/-- **WS-ZA ZA5.4 part 14: the CNode a carve makes** — `2 ^ radixBits` empty
slots, no guard, resolving exactly its radix bits: the CNode seL4's
`createObject` makes for `seL4_CapTableObject`, whose capability carries guard
size 0. -/
def carvedCNode (radixBits : Nat) : CNode :=
  CNode.ofSlots radixBits 0 0 radixBits SeLe4n.UniqueSlotMap.empty

/-- **WS-BP BP7.1 slice 4 (`v0.36.8`), every kind since WS-ZA ZA5.4 part 14:
what a carve can make.**

The four kinds an untyped's memory backs *as memory*: a frame (one page a thread
maps), a child untyped (a sub-region it carves from in turn), and — since slice 4b
(`v0.36.10`) and `v0.36.12` — a VSpace root and an intermediate page table, each
one page of translation table.  Since part 14 also every kernel object, as
seL4's `Untyped_Retype` makes them (decided by Adam, 2026-10-21: "carve every
kind"): a thread, an endpoint, a notification, a CNode of a chosen radix, a
reply and a scheduling context of a chosen size, each of seL4's size
(`CarveRequest.size`) and on a multiple of it (`requiresSizeAlignment`).  A
request is built only by the syscall arm's decode (`carveRequestOf?`), which
bounds the sizes the caller names and supplies what the creating core decides;
every other guard — authority, capacity, fresh id, device rule, alignment,
region — is the carve primitive's. -/
inductive CarveRequest where
  | frame
  | untyped (sizeBits : Nat)
  /-- **WS-BP BP7.1 slice 4b (`v0.36.10`)**: a VSpace root — one page, its
      top-level translation table — registered under `asid`, which the arm
      chooses (`freshAsid?`) and the carve checks is free
      (`CarveRequest.admissible`). -/
  | vspaceRoot (asid : SeLe4n.ASID)
  /-- **WS-BP BP7.1 (`v0.36.12`)**: an intermediate translation table — one page,
      installed into an address space by `.pageTableMap`. -/
  | pageTable
  /-- **WS-ZA ZA5.4 part 14**: a thread (`carvedTcb`), in the domain of the
      core that carves it and with that core as its affinity. -/
  | tcb (domain : SeLe4n.DomainId) (core : SeLe4n.Kernel.Concurrency.CoreId)
  /-- An endpoint with both queues empty. -/
  | endpoint
  /-- A notification, idle, with no waiter and no pending badge. -/
  | notification
  /-- A CNode of `2 ^ radixBits` empty slots (`carvedCNode`). -/
  | cnode (radixBits : Nat)
  /-- A reply with no caller and no stack link. -/
  | reply
  /-- A scheduling context of `2 ^ sizeBits` bytes, with no budget and no
      bound thread. -/
  | schedContext (sizeBits : Nat)
  deriving Repr, DecidableEq

/-- **WS-BP BP7.1 (`v0.36.12`): the page table a carve makes** — installed
nowhere, on the page at the free index, the same page
`untypedNextFrame` names.  WS-ZA ZA5.4: with its own slot cell
(`PageTableObject.slotCell`), built from the page's address so that it is the
table's own and not the default's shared constant: the cell is part of the
table's memory, carved with it, and its first install writes over it. -/
def untypedNextPageTable (ut : UntypedObject) (idx : Nat) : PageTableObject :=
  { base := (untypedNextFrame ut idx).base
    slotCell := Squash.mk [⟨0, 0, SeLe4n.ObjId.ofNat (untypedNextFrame ut idx).base.toNat⟩] }

/-- **WS-BP BP7.1 (`v0.36.12`): the capability a carve hands back for a page
table.**  Read and write — `.pageTableMap` and `.pageTableUnmap` ask `.write`.
`.retype` is absent: a table's page returns to its untyped through the reset. -/
def pageTableCapability (tableId : SeLe4n.ObjId) : Capability :=
  { target := .object tableId
    rights := AccessRightSet.ofList [.read, .write] }

/-- **WS-BP BP7.1 slice 4b (`v0.36.10`): the VSpace root a carve makes** — no
mappings, registered under `asid`, and its **table base the page at the
untyped's free index**, the same page `untypedNextFrame` names, so the root owns
exactly one page its untyped owned.  seL4's VSpace object is that page. -/
def untypedNextVSpaceRoot (ut : UntypedObject) (idx : Nat) (asid : SeLe4n.ASID) : VSpaceRoot :=
  { asid := asid, mappings := {}, tableBase := some (untypedNextFrame ut idx).base }

/-- **WS-BP BP7.1 slice 4b: the capability a carve hands back for a VSpace
root.**  Read and write — the rights `.vspaceMap` and `.vspaceUnmap` ask of an
address-space capability.  `.retype` is absent: a root's page returns to its
untyped through the reset. -/
def vspaceRootCapability (rootId : SeLe4n.ObjId) : Capability :=
  { target := .object rootId
    rights := AccessRightSet.ofList [.read, .write] }

/-- **WS-BP BP7.1 slice 4b (`v0.36.10`): an ASID nothing holds.**  The least
`n` in `[1, maxASID)` the ASID table does not map.  ASID `0` is never chosen —
it is the boot VSpace root's, and ARM64 reserves it — and the bound is the
machine's, the one `.vspaceMap`'s decode reads.  `none` when every ASID is
taken.  A linear scan bounded by the ASID width, as seL4's `ASIDPool_Assign`
scans its pool.

The scan is `freshAsidFrom`, a tail call per candidate, so it allocates
nothing and stops at the first free ASID (PR #904 review): the retired
spelling `(List.range st.machine.maxASID).find? …` built the whole range —
65,536 list cells on the production configurations — before the search could
stop, on every VSpace-root carve, inside the kernel-entry lock.  Its
worst case, every ASID but the last taken, is still `maxASID` table lookups
and no allocation. -/
def freshAsidFrom (st : SystemState) : Nat → Nat → Option SeLe4n.ASID
  | 0, _ => none
  | fuel + 1, n =>
      if n < st.machine.maxASID then
        if (st.asidTable[SeLe4n.ASID.ofNat n]?).isNone then some (SeLe4n.ASID.ofNat n)
        else freshAsidFrom st fuel (n + 1)
      else none

/-- See `freshAsidFrom`: the scan starts at `1` with one step of fuel per ASID. -/
def freshAsid? (st : SystemState) : Option SeLe4n.ASID :=
  freshAsidFrom st st.machine.maxASID 1

/-- Every ASID the scan answers is at least its start, below the machine's
bound, and free in the ASID table. -/
theorem freshAsidFrom_spec (st : SystemState) :
    ∀ (fuel n : Nat) (asid : SeLe4n.ASID), freshAsidFrom st fuel n = some asid →
      n ≤ asid.toNat ∧ asid.toNat < st.machine.maxASID ∧
        (st.asidTable[asid]?).isNone = true
  | 0, _, _, h => by simp [freshAsidFrom] at h
  | fuel + 1, n, asid, h => by
    unfold freshAsidFrom at h
    by_cases hLt : n < st.machine.maxASID
    · rw [if_pos hLt] at h
      by_cases hFree : (st.asidTable[SeLe4n.ASID.ofNat n]?).isNone = true
      · rw [if_pos hFree] at h
        cases h
        exact ⟨Nat.le_refl _, hLt, hFree⟩
      · rw [if_neg hFree] at h
        have ⟨h1, h2, h3⟩ := freshAsidFrom_spec st fuel (n + 1) asid h
        exact ⟨by omega, h2, h3⟩
    · rw [if_neg hLt] at h; cases h

/-- **WS-BP BP7.1 slice 4b: is a request's own precondition met?**  A frame or a
child untyped has none beyond the primitive's.  A VSpace root's ASID must be
non-zero, below the machine's bound, and free in the ASID table — decided here,
by the carve, rather than trusted of whoever chose it: `storeObject` inserts a
root's ASID unconditionally, and an ASID already held would move its entry to
the new root. -/
def CarveRequest.admissible (st : SystemState) : CarveRequest → Bool
  | .frame => true
  | .untyped _ => true
  | .vspaceRoot asid =>
      asid.toNat != 0 && decide (asid.toNat < st.machine.maxASID) &&
        (st.asidTable[asid]?).isNone
  | .pageTable => true
  | .tcb _ _ => true
  | .endpoint => true
  | .notification => true
  | .cnode _ => true
  | .reply => true
  | .schedContext _ => true

/-- The type of the object a request carves, read without building it
(`CarveRequest.object_objectType`).  WS-ZA ZA5.4. -/
def CarveRequest.objectType : CarveRequest → KernelObjectType
  | .frame => .frame
  | .untyped _ => .untyped
  | .vspaceRoot _ => .vspaceRoot
  | .pageTable => .pageTable
  | .tcb _ _ => .tcb
  | .endpoint => .endpoint
  | .notification => .notification
  | .cnode _ => .cnode
  | .reply => .reply
  | .schedContext _ => .schedContext

/-- The object a request carves out of `ut` (stored at `untypedId`) at free
index `idx`, to be stored at `childId`.  A kernel object carries the id it is
stored at as its own identity (`KernelObject.embeddedIdentityMatches`). -/
def CarveRequest.object (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject) (idx : Nat) :
    CarveRequest → KernelObject
  | .frame => .frame (untypedNextFrame ut idx)
  | .untyped b => .untyped (untypedNextChild ut idx untypedId b)
  | .vspaceRoot asid => .vspaceRoot (untypedNextVSpaceRoot ut idx asid)
  | .pageTable => .pageTable (untypedNextPageTable ut idx)
  | .tcb dom core => .tcb (carvedTcb childId dom core)
  | .endpoint => .endpoint (Endpoint.ofQueues {} {})
  | .notification => .notification ({ state := .idle } : Notification)
  | .cnode r => .cnode (carvedCNode r)
  | .reply => .reply (SeLe4n.Kernel.Reply.empty (SeLe4n.ReplyId.ofObjId childId))
  | .schedContext _ =>
      .schedContext (SeLe4n.Kernel.SchedContext.empty (SeLe4n.SchedContextId.ofObjId childId))

theorem CarveRequest.object_objectType (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject)
    (idx : Nat) (req : CarveRequest) :
    (req.object untypedId childId ut idx).objectType = req.objectType := by
  cases req <;> rfl

/-- A carved object carries the id it is stored at: the runtime half of the
agreement the boot enforces with `embeddedIdentitiesMatchSlots`. -/
theorem CarveRequest.object_embeddedIdentityMatches (untypedId childId : SeLe4n.ObjId)
    (ut : UntypedObject) (idx : Nat) (req : CarveRequest) :
    (req.object untypedId childId ut idx).embeddedIdentityMatches childId = true := by
  cases req <;> simp [CarveRequest.object, KernelObject.embeddedIdentityMatches, carvedTcb,
    SeLe4n.Kernel.Reply.empty, SeLe4n.Kernel.SchedContext.empty]

/-- The bytes a request takes from the parent's region: a page for the page
kinds, `2 ^ b` for a child untyped, and seL4's `getObjectSize` for a kernel
object (`objectTypeAllocSize` for the fixed-size ones). -/
def CarveRequest.size : CarveRequest → Nat
  | .frame => SeLe4n.pageBytes
  | .untyped b => 2 ^ b
  | .vspaceRoot _ => SeLe4n.pageBytes
  | .pageTable => SeLe4n.pageBytes
  | .tcb _ _ => objectTypeAllocSize .tcb
  | .endpoint => objectTypeAllocSize .endpoint
  | .notification => objectTypeAllocSize .notification
  | .cnode r => 2 ^ (r + cnodeSlotBits)
  | .reply => objectTypeAllocSize .reply
  | .schedContext b => 2 ^ b

/-- The rights of the capability a request hands back (`CarveRequest.capability_eq`),
so the capability is written into its slot as fields.  WS-ZA ZA5.4. -/
def CarveRequest.rights : CarveRequest → AccessRightSet
  | .frame => AccessRightSet.ofList [.read, .write, .grant]
  | .untyped _ => AccessRightSet.ofList [.read, .write, .retype]
  | .vspaceRoot _ => AccessRightSet.ofList [.read, .write]
  | .pageTable => AccessRightSet.ofList [.read, .write]
  | .tcb _ _ => kernelObjectRights
  | .endpoint => kernelObjectRights
  | .notification => kernelObjectRights
  | .cnode _ => kernelObjectRights
  | .reply => kernelObjectRights
  | .schedContext _ => kernelObjectRights

/-- The capability a request hands back for the carved object: the memory
kinds' own (`frameCapability`, `untypedCapability`, `vspaceRootCapability`,
`pageTableCapability`) and, for a kernel object, `kernelObjectRights` to it. -/
def CarveRequest.capability (childId : SeLe4n.ObjId) : CarveRequest → Capability
  | .frame => frameCapability childId
  | .untyped _ => untypedCapability childId
  | .vspaceRoot _ => vspaceRootCapability childId
  | .pageTable => pageTableCapability childId
  | .tcb _ _ => kernelObjectCapability childId
  | .endpoint => kernelObjectCapability childId
  | .notification => kernelObjectCapability childId
  | .cnode _ => kernelObjectCapability childId
  | .reply => kernelObjectCapability childId
  | .schedContext _ => kernelObjectCapability childId

theorem CarveRequest.capability_eq (childId : SeLe4n.ObjId) (req : CarveRequest) :
    req.capability childId = { target := .object childId, rights := req.rights } := by
  cases req <;> rfl

/-- The memory write a request performs.  A RAM frame's page is zeroed before
any capability to it exists (`carveZeroFrame`).  A child untyped writes nothing:
its memory is handed out only through its own carves, and each frame carve
zeroes its page, so scrubbing here would scrub twice — and a device child's
memory is MMIO, where a store is a command.  Every scrub is also recorded as a
physical write (WS-BP BP7.2), since the model's memory is not the machine's.  A
VSpace root's page is zeroed too
(slice 4b): a zeroed table page is a table of invalid descriptors, so a PE told
to walk it translates nothing — and a device untyped cannot back a root at all
(`KernelObjectType.deviceBackable`), so the page is always RAM. -/
def CarveRequest.scrub (st : SystemState) (ut : UntypedObject) (idx : Nat) :
    CarveRequest → SystemState
  | .frame => carveZeroFrame st (untypedNextFrame ut idx)
  | .untyped _ => st
  -- WS-ZA ZA5.4 part 14: a kernel object is the store's record, never mapped:
  -- no capability names its memory as memory, so nothing a thread can read
  -- is written.  Its memory returns through the reset, and a frame carved
  -- from it later zeroes its own page.
  | .tcb _ _ | .endpoint | .notification | .cnode _ | .reply | .schedContext _ => st
  | .vspaceRoot _ =>
      { st with
          machine := SeLe4n.zeroMemoryRange st.machine (untypedNextFrame ut idx).base SeLe4n.pageBytes
          physicalWrites := st.physicalWrites.pushAfter st.physicalWritesDrained
            (SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage (untypedNextFrame ut idx).base)
          physicalWritesDrained := false }
  -- WS-BP BP7.1 (`v0.36.12`): a table page is zeroed for the root's reason — a
  -- zeroed table holds only invalid descriptors.
  | .pageTable =>
      { st with
          machine := SeLe4n.zeroMemoryRange st.machine (untypedNextFrame ut idx).base SeLe4n.pageBytes
          physicalWrites := st.physicalWrites.pushAfter st.physicalWritesDrained
            (SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage (untypedNextFrame ut idx).base)
          physicalWritesDrained := false }

/-- **WS-BP BP7.1 (`v0.36.5`, generalized at slice 4, `v0.36.8`): carve one object
out of an untyped the caller holds — seL4's `Untyped_Retype`.**

`src` is the slot of the untyped capability the syscall was invoked on, `childId`
the object id the carved object takes, `dst` the empty slot its capability goes
to, and `req` what is carved — a frame, or a child untyped of `2 ^ b` bytes.
Four steps, and every refusal commits nothing:

1. **The carve** is `retypeFromUntyped` at `req.object untypedId childId ut idx` and
   `req.size` bytes, where `idx` is the invoked capability's free index — so the
   authority check (`lifecycleRetypeAuthority`: the capability names this untyped
   and carries `.retype`), the capacity, fresh-id and self-overwrite guards, the
   device rule (a device untyped backs memory-backed kinds only), page alignment,
   the minimum size and the advance of the capability's free index in its slot
   are the primitive's own, not a second copy.  The carved object's base is the
   free index before the advance, which is the offset `allocate` records for the
   child.
2. **The scrub** (`req.scrub`): a RAM frame's page is zeroed; a child untyped is
   not written.
3. **The capability**: `req.capability childId` is written into `dst`, which
   must be an empty slot its CNode can address — `cspaceInsertSlot`'s refusals
   (`cspaceDstRefusal`), asked of the state the retype was handed, before the
   carve writes anything, as seL4's `decodeUntypedInvocation` checks the
   destination slots before `invokeUntyped` (WS-ZA ZA5.4: every check precedes
   every write, so the writes are made in place).
4. **The derivation**: the new capability is recorded as a CDT child of the
   untyped capability (`DerivationOp.retype`), so revoking the untyped
   capability reaches it — the edge every other install path records.

This is the only path that creates an object on a live state, of every kind:
the boot refuses configured frames and requires every boot untyped pristine,
so every object a live transition creates was carved from an untyped by a
holder of a capability to it.

*Tombstone:* `untypedRetypeFrame` (`v0.36.5`–`v0.36.7`) was this operation at
`req = .frame`; it is deleted rather than kept beside the general carve. -/
def untypedRetypeObject (src : CSpaceAddr) (childId : SeLe4n.ObjId)
    (dst : CSpaceAddr) (req : CarveRequest) : Kernel Unit :=
  fun st =>
    if !req.admissible st then .error .illegalState else
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (utCap, _) =>
      match utCap.target with
      | .object untypedId =>
        -- Authority first: a capability without `.retype` learns nothing about
        -- the object it names, the child id or the destination.
        if !lifecycleRetypeAuthority utCap untypedId then .error .illegalAuthority else
        match st.getUntyped? untypedId with
        | none => .error .untypedTypeMismatch
        | some ut =>
          match cspaceDstRefusal dst st with
          | .error e => .error e
          | .ok () =>
            match retypeFromUntyped src untypedId childId (req.object untypedId childId ut utCap.freeIndex)
                req.size st with
            | .error e => .error e
            | .ok ((), st1) =>
              .ok ((), ((req.scrub st1 ut utCap.freeIndex).storeCNodeWith dst.cnode
                (·.insert dst.slot (req.capability childId))).cdtAddChild src dst .retype)
      | _ => .error .invalidCapability


/-- **WS-BP BP7.1**: a successful carve of a page-aligned kind found the
authority capability's free index on a page boundary — the primitive's S5-G
guard, read back.  It is what makes the base of a carved frame a page a
descriptor can name. -/
theorem retypeFromUntyped_ok_aligned
    (st st' : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (newObj : KernelObject) (allocSize : Nat)
    (ut : UntypedObject) (cap : Capability)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hLk : cspaceLookupSlot authority st = .ok (cap, st))
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    carveBaseAligned newObj.objectType allocSize ut cap.freeIndex = true := by
  cases hA : carveBaseAligned newObj.objectType allocSize ut cap.freeIndex
  · exfalso
    unfold retypeFromUntyped SystemState.getObject? at hStep
    simp only [hObj, hLk, hA, Bool.not_false, ↓reduceIte] at hStep
    repeat (split at hStep <;> (try cases hStep))
    all_goals cases hStep
  · rfl

theorem retypeFromUntyped_ok_pageAligned
    (st st' : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (newObj : KernelObject) (allocSize : Nat)
    (ut : UntypedObject) (cap : Capability)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hLk : cspaceLookupSlot authority st = .ok (cap, st))
    (hReq : requiresPageAlignment newObj.objectType = true)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    allocationBasePageAligned ut cap.freeIndex = true := by
  rw [← carveBaseAligned_of_page hReq allocSize]
  exact retypeFromUntyped_ok_aligned st st' authority untypedId childId newObj allocSize ut cap
    hObj hLk hStep

/-- **WS-ZA ZA5.4 part 14**: a successful carve of a kernel kind found its base on
a multiple of the carve's size — seL4's placement of every object. -/
theorem retypeFromUntyped_ok_sizeAligned
    (st st' : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (newObj : KernelObject) (allocSize : Nat)
    (ut : UntypedObject) (cap : Capability)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hLk : cspaceLookupSlot authority st = .ok (cap, st))
    (hReq : requiresSizeAlignment newObj.objectType = true)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    (ut.regionBase.toNat + cap.freeIndex) % allocSize = 0 := by
  have h := retypeFromUntyped_ok_aligned st st' authority untypedId childId newObj allocSize ut cap
    hObj hLk hStep
  have hNp : requiresPageAlignment newObj.objectType = false := by
    revert hReq; cases newObj.objectType <;> simp [requiresSizeAlignment, requiresPageAlignment]
  simpa [carveBaseAligned, hNp, hReq] using h


/-- **WS-BP BP7.1 slice 4**: a request's scrub moves no object... -/
@[simp] theorem CarveRequest.scrub_objects (st : SystemState) (ut : UntypedObject) (idx : Nat)
    (req : CarveRequest) : (req.scrub st ut idx).objects = st.objects := by
  cases req <;> simp only [CarveRequest.scrub, carveZeroFrame] <;> (try split) <;> rfl

/-- ...and no scheduler state. -/
@[simp] theorem CarveRequest.scrub_scheduler (st : SystemState) (ut : UntypedObject) (idx : Nat)
    (req : CarveRequest) : (req.scrub st ut idx).scheduler = st.scheduler := by
  cases req <;> simp only [CarveRequest.scrub, carveZeroFrame] <;> (try split) <;> rfl

/-- **WS-ZA ZA5.4: what a successful carve writes** — `untypedRetypeObject`
read back on the state it was handed: the destination admitted there, the
carve, and the capability written into the destination slot over the scrubbed
state (`storeCNodeWith`), then its derivation edge.  Needs no invariant, so the
in-place form is proven equal to it unconditionally. -/
theorem untypedRetypeObject_ok_writes
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (req : CarveRequest)
    (st st' : SystemState)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    ∃ (utCap : Capability) (untypedId : SeLe4n.ObjId) (ut : UntypedObject)
      (st1 : SystemState),
      cspaceLookupSlot src st = .ok (utCap, st) ∧
      utCap.target = .object untypedId ∧
      st.getUntyped? untypedId = some ut ∧
      cspaceDstAdmitted dst st = true ∧
      retypeFromUntyped src untypedId childId (req.object untypedId childId ut utCap.freeIndex) req.size st
        = .ok ((), st1) ∧
      st' = ((req.scrub st1 ut utCap.freeIndex).storeCNodeWith dst.cnode
        (·.insert dst.slot (req.capability childId))).cdtAddChild src dst .retype := by
  unfold untypedRetypeObject at hStep
  cases hAdm : req.admissible st
  · simp only [hAdm, Bool.not_false, ↓reduceIte] at hStep; cases hStep
  simp only [hAdm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
  cases hLk : cspaceLookupSlot src st with
  | error e => rw [hLk] at hStep; cases hStep
  | ok pair =>
    obtain ⟨utCap, stL⟩ := pair
    have hStL : stL = st := cspaceLookupSlot_ok_state_eq st src utCap stL hLk
    subst hStL
    rw [hLk] at hStep
    simp only at hStep
    cases hTgt : utCap.target with
    | object untypedId =>
      rw [hTgt] at hStep
      simp only at hStep
      cases hAu : lifecycleRetypeAuthority utCap untypedId
      · simp only [hAu, Bool.not_false, ↓reduceIte] at hStep; cases hStep
      simp only [hAu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
      cases hUt : stL.getUntyped? untypedId with
      | none => rw [hUt] at hStep; cases hStep
      | some ut =>
        rw [hUt] at hStep
        simp only at hStep
        cases hD : cspaceDstRefusal dst stL with
        | error e => rw [hD] at hStep; cases hStep
        | ok u =>
          cases u
          rw [hD] at hStep
          simp only at hStep
          cases hRt : retypeFromUntyped src untypedId childId
              (req.object untypedId childId ut utCap.freeIndex) req.size stL with
          | error e => rw [hRt] at hStep; cases hStep
          | ok p1 =>
            obtain ⟨_, st1⟩ := p1
            rw [hRt] at hStep
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
            exact ⟨utCap, untypedId, ut, st1, by first | exact hLk | rfl,
              by first | exact hTgt | rfl, by first | exact hUt | rfl,
              (cspaceDstRefusal_eq_ok_iff dst stL).mp hD,
              by first | exact hRt | rfl, hStep.symm⟩
    | _ => rw [hTgt] at hStep; cases hStep

/-- **WS-BP BP7.1: what a successful carve consists of** — the four steps of
`untypedRetypeObject`, read back.  The capability lookup returns the state it
was given, so every later step runs from `st` itself.  One owner for the case
analysis, so the invariant proofs that consume a carve read these equations
rather than re-running the operation's `match`.  The destination checked
before the carve is still admitted after it — the carve writes the untyped and
a fresh id, neither of them a CNode — so the write is `cspaceInsertSlot`'s. -/
theorem untypedRetypeObject_ok_decompose
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (req : CarveRequest)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    ∃ (utCap : Capability) (untypedId : SeLe4n.ObjId) (ut : UntypedObject)
      (st1 st2 : SystemState),
      cspaceLookupSlot src st = .ok (utCap, st) ∧
      utCap.target = .object untypedId ∧
      st.getUntyped? untypedId = some ut ∧
      retypeFromUntyped src untypedId childId (req.object untypedId childId ut utCap.freeIndex) req.size st
        = .ok ((), st1) ∧
      cspaceInsertSlot dst (req.capability childId) (req.scrub st1 ut utCap.freeIndex)
        = .ok ((), st2) ∧
      st' = st2.cdtAddChild src dst .retype := by
  obtain ⟨utCap, untypedId, ut, st1, hLk, hTgt, hUt, hD, hRt, rfl⟩ :=
    untypedRetypeObject_ok_writes src dst childId req st st' hStep
  have hFresh := retypeFromUntyped_childId_fresh src untypedId childId _ _ st st1 hRt
  obtain ⟨_, _, _, stL, stUt, _, stCh, _, _, _, hLkR, _, _, hStUt, hStCh, hIdx⟩ :=
    retypeFromUntyped_ok_decompose st st1 src untypedId childId _ _ hRt
  rw [cspaceLookupSlot_ok_state_eq st src _ stL hLkR] at hStUt
  have hObjU : st.objects[untypedId]? = some (.untyped ut) :=
    (SystemState.getUntyped?_eq_some_iff st untypedId ut).mp hUt
  have hInvUt := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStUt
  have hInvCh := storeObject_preserves_objects_invExt _ _ _ _ hInvUt hStCh
  have hDCh : cspaceDstAdmitted dst stCh = true := by
    unfold cspaceDstAdmitted at hD ⊢
    cases hC : st.getCNode? dst.cnode with
    | none => rw [hC] at hD; cases hD
    | some cn =>
      have hObjC : st.objects[dst.cnode]? = some (.cnode cn) :=
        (SystemState.getCNode?_eq_some_iff st dst.cnode cn).mp hC
      have hNeU : dst.cnode ≠ untypedId := by
        intro h; rw [h, hObjU] at hObjC; cases hObjC
      have hNeC : dst.cnode ≠ childId := by
        intro h; rw [h] at hObjC; rw [hObjC] at hFresh; cases hFresh
      have hC1 : stCh.getCNode? dst.cnode = some cn := by
        rw [SystemState.getCNode?_eq_some_iff,
          storeObject_objects_ne _ _ _ _ _ hNeC hInvUt hStCh,
          storeObject_objects_ne _ _ _ _ _ hNeU hObjInv hStUt, hObjC]
      rw [hC] at hD; rw [hC1]; exact hD
  have hD1 : cspaceDstAdmitted dst st1 = true := by
    rw [hIdx]; exact setCapFreeIndex_preserves_dstAdmitted hInvCh hDCh
  have hD' : cspaceDstAdmitted dst (req.scrub st1 ut utCap.freeIndex) = true := by
    have hG : (req.scrub st1 ut utCap.freeIndex).getCNode? dst.cnode = st1.getCNode? dst.cnode := by
      unfold SystemState.getCNode?; rw [CarveRequest.scrub_objects]
    unfold cspaceDstAdmitted at hD1 ⊢; rw [hG]; exact hD1
  exact ⟨utCap, untypedId, ut, st1, _, hLk, hTgt, hUt, hRt,
    cspaceInsertSlot_of_admitted hD' _, rfl⟩

/-- **WS-BP BP7.1 slice 4b: a successful carve met its request's own
precondition** — for a VSpace root, its ASID was non-zero, in range and free. -/
theorem untypedRetypeObject_ok_admissible
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (req : CarveRequest)
    (st st' : SystemState)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    req.admissible st = true := by
  unfold untypedRetypeObject at hStep
  cases hAdm : req.admissible st
  · simp only [hAdm, Bool.not_false, ↓reduceIte] at hStep; cases hStep
  · rfl

/-- **WS-ZA ZA5.4 part 14: the carve asks authority before it reads anything
the caller named.**  An admissible request through a capability that names an
object without the `.retype` right is refused with `.illegalAuthority`, whatever
the object, the child id and the destination are — so the refusal answers no
question about any of them. -/
theorem untypedRetypeObject_unauthorized
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (req : CarveRequest)
    (st : SystemState) (cap : Capability) (untypedId : SeLe4n.ObjId)
    (hAdm : req.admissible st = true)
    (hLk : cspaceLookupSlot src st = .ok (cap, st))
    (hTgt : cap.target = .object untypedId)
    (hAu : lifecycleRetypeAuthority cap untypedId = false) :
    untypedRetypeObject src childId dst req st = .error .illegalAuthority := by
  unfold untypedRetypeObject
  simp only [hAdm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hLk, hTgt, hAu,
    Bool.not_false]

/-- **WS-BP BP7.1 slice 4b: `freshAsid?` answers an ASID a VSpace-root carve
admits** — non-zero, below the machine's bound, and free in the ASID table. -/
theorem freshAsid?_admissible (st : SystemState) (asid : SeLe4n.ASID)
    (h : freshAsid? st = some asid) :
    (CarveRequest.vspaceRoot asid).admissible st = true := by
  have ⟨h1, h2, h3⟩ := freshAsidFrom_spec st _ 1 asid h
  simp only [CarveRequest.admissible, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq]
  exact ⟨⟨by omega, h2⟩, h3⟩

/-- **WS-BP BP7.1: the carved frame's page is inside its untyped, on a page
boundary, and of its untyped's memory kind.**  The whole of what "memory is
authority" asks of a carve: the frame names one page the untyped owned
(`[regionBase, regionBase + regionSize)`), a descriptor can name it, and a
device untyped cannot be turned into RAM or the reverse. -/
theorem untypedNextFrame_of_retype_ok
    (st st' : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject) (cap : Capability)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hLk : cspaceLookupSlot authority st = .ok (cap, st))
    (hStep : retypeFromUntyped authority untypedId childId
      (.frame (untypedNextFrame ut cap.freeIndex)) SeLe4n.pageBytes st = .ok ((), st')) :
    ut.regionBase.toNat ≤ (untypedNextFrame ut cap.freeIndex).base.toNat ∧
    (untypedNextFrame ut cap.freeIndex).base.toNat + SeLe4n.pageBytes ≤
      ut.regionBase.toNat + ut.regionSize ∧
    (untypedNextFrame ut cap.freeIndex).wellFormed ∧
    (untypedNextFrame ut cap.freeIndex).isDevice = ut.isDevice := by
  obtain ⟨ut₀, ut', cap₀, _, _, offset, _, hObj₀, _, _, hLk₀, _, hAlloc, _, _, _⟩ :=
    retypeFromUntyped_ok_decompose st st' authority untypedId childId _ _ hStep
  rw [hObj] at hObj₀
  have hEq : ut₀ = ut := by cases hObj₀; rfl
  subst hEq
  rw [hLk] at hLk₀
  have hEqC : cap₀ = cap := by cases hLk₀; rfl
  subst hEqC
  have hAligned := retypeFromUntyped_ok_pageAligned st st' authority untypedId childId
    _ _ ut₀ cap₀ hObj hLk rfl hStep
  have hCan := ((UntypedObject.allocate_some_iff ut₀ cap₀.freeIndex childId _ _).mp hAlloc).1
  simp only [UntypedObject.canAllocate, Bool.and_eq_true, decide_eq_true_eq] at hCan
  simp only [allocationBasePageAligned, beq_iff_eq] at hAligned
  refine ⟨?_, ?_, ?_, rfl⟩
  · show ut₀.regionBase.toNat ≤ ut₀.regionBase.toNat + cap₀.freeIndex
    omega
  · show ut₀.regionBase.toNat + cap₀.freeIndex + SeLe4n.pageBytes ≤ _
    omega
  · show (ut₀.regionBase.toNat + cap₀.freeIndex) % SeLe4n.pageBytes = 0
    simpa [SeLe4n.pageBytes] using hAligned


/-- **WS-BP BP7.1 slice 4b (`v0.36.10`): a carved VSpace root's table page is
inside its untyped, on a page boundary, and RAM.**  The root counterpart of
`untypedNextFrame_of_retype_ok`: the page a PE will be told to walk is one page
the untyped owned, a descriptor base can name it, and it is never MMIO — a
device untyped cannot back a root (`KernelObjectType.deviceBackable`). -/
theorem untypedNextVSpaceRoot_of_retype_ok
    (st st' : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject) (cap : Capability)
    (asid : SeLe4n.ASID)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hLk : cspaceLookupSlot authority st = .ok (cap, st))
    (hStep : retypeFromUntyped authority untypedId childId
      (.vspaceRoot (untypedNextVSpaceRoot ut cap.freeIndex asid)) SeLe4n.pageBytes st
        = .ok ((), st')) :
    (untypedNextVSpaceRoot ut cap.freeIndex asid).tableBase =
      some (untypedNextFrame ut cap.freeIndex).base ∧
    ut.regionBase.toNat ≤ (untypedNextFrame ut cap.freeIndex).base.toNat ∧
    (untypedNextFrame ut cap.freeIndex).base.toNat + SeLe4n.pageBytes ≤
      ut.regionBase.toNat + ut.regionSize ∧
    (untypedNextFrame ut cap.freeIndex).base.toNat % SeLe4n.pageBytes = 0 ∧
    ut.isDevice = false := by
  obtain ⟨ut₀, ut', cap₀, _, _, offset, _, hObj₀, hDev, _, hLk₀, _, hAlloc, _, _, _⟩ :=
    retypeFromUntyped_ok_decompose st st' authority untypedId childId _ _ hStep
  rw [hObj] at hObj₀
  have hEq : ut₀ = ut := by cases hObj₀; rfl
  subst hEq
  rw [hLk] at hLk₀
  have hEqC : cap₀ = cap := by cases hLk₀; rfl
  subst hEqC
  have hAligned := retypeFromUntyped_ok_pageAligned st st' authority untypedId childId
    _ _ ut₀ cap₀ hObj hLk rfl hStep
  have hCan := ((UntypedObject.allocate_some_iff ut₀ cap₀.freeIndex childId _ _).mp hAlloc).1
  simp only [UntypedObject.canAllocate, Bool.and_eq_true, decide_eq_true_eq] at hCan
  simp only [allocationBasePageAligned, beq_iff_eq] at hAligned
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · show ut₀.regionBase.toNat ≤ ut₀.regionBase.toNat + cap₀.freeIndex
    omega
  · show ut₀.regionBase.toNat + cap₀.freeIndex + SeLe4n.pageBytes ≤ _
    omega
  · show (ut₀.regionBase.toNat + cap₀.freeIndex) % SeLe4n.pageBytes = 0
    simpa [SeLe4n.pageBytes] using hAligned
  · rcases hDev with h | h
    · exact h
    · simp [KernelObject.objectType, KernelObjectType.deviceBackable] at h

/-- **WS-BP BP7.1**: the scrub moves no object. -/
@[simp] theorem carveZeroFrame_objects (st : SystemState) (frame : FrameObject) :
    (carveZeroFrame st frame).objects = st.objects := by
  unfold carveZeroFrame; split <;> rfl

/-- **WS-BP BP7.1**: ...and no scheduler state. -/
@[simp] theorem carveZeroFrame_scheduler (st : SystemState) (frame : FrameObject) :
    (carveZeroFrame st frame).scheduler = st.scheduler := by
  unfold carveZeroFrame; split <;> rfl

/-- **WS-BP BP7.1**: ...and every other field but `machine` and the physical-write
ledger (WS-BP BP7.2) — the record is the input with the machine's memory
rewritten and the scrub recorded, or the input itself. -/
theorem carveZeroFrame_eq (st : SystemState) (frame : FrameObject) :
    carveZeroFrame st frame =
      { st with machine := (carveZeroFrame st frame).machine
                physicalWrites := (carveZeroFrame st frame).physicalWrites
                physicalWritesDrained := (carveZeroFrame st frame).physicalWritesDrained } := by
  unfold carveZeroFrame; split <;> rfl

/-- **WS-BP BP7.1**: a RAM frame's page is zero after the scrub. -/
theorem carveZeroFrame_zeroed (st : SystemState) (frame : FrameObject)
    (hRam : frame.isDevice = false) :
    SeLe4n.memoryZeroed (carveZeroFrame st frame).machine frame.base SeLe4n.pageBytes := by
  unfold carveZeroFrame
  simp only [hRam, Bool.false_eq_true, ↓reduceIte]
  exact SeLe4n.zeroMemoryRange_establishes_memoryZeroed st.machine _ _

/-- **WS-BP post-landing audit (`v0.36.32`)**: the scrub of a RAM frame records
exactly one physical write, the zeroing of the frame's own page — the write
whose `PhysicalWrite.icacheMaintenance` is the frame's clean-to-PoU
(`carveZeroFrame_discharges_carveScrub_obligation`). -/
theorem carveZeroFrame_pendingPhysicalWrites (st : SystemState) (frame : FrameObject)
    (hRam : frame.isDevice = false) :
    (carveZeroFrame st frame).pendingPhysicalWrites =
      st.pendingPhysicalWrites ++
        [SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage frame.base] := by
  unfold carveZeroFrame
  simp only [hRam, Bool.false_eq_true, ↓reduceIte, SystemState.pendingPhysicalWrites,
    SeLe4n.Kernel.Architecture.PhysicalWriteLedger.toList_pushAfter]

/-- **WS-BP post-landing audit (`v0.36.32`)**: a device frame's scrub records
nothing — its page is MMIO, where a store is a command — so it owes no
maintenance either. -/
theorem carveZeroFrame_device (st : SystemState) (frame : FrameObject)
    (hDev : frame.isDevice = true) : carveZeroFrame st frame = st := by
  unfold carveZeroFrame
  simp only [hDev, ↓reduceIte]

/-- **WS-BP BP7.1 slice 4: the carved child untyped's region is inside its
parent, on a page boundary, of its parent's memory kind, with its parent stamped
and nothing carved from it.**  The child-untyped counterpart of
`untypedNextFrame_of_retype_ok`, and the fact the reset's containment check
(`untypedSubtreeContained`) decides on every state rather than trusting. -/
theorem untypedNextChild_of_retype_ok
    (st st' : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject) (cap : Capability) (b : Nat)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hLk : cspaceLookupSlot authority st = .ok (cap, st))
    (hStep : retypeFromUntyped authority untypedId childId
      (.untyped (untypedNextChild ut cap.freeIndex untypedId b)) (2 ^ b) st = .ok ((), st')) :
    ut.regionBase.toNat ≤ (untypedNextChild ut cap.freeIndex untypedId b).regionBase.toNat ∧
    (untypedNextChild ut cap.freeIndex untypedId b).regionBase.toNat +
        (untypedNextChild ut cap.freeIndex untypedId b).regionSize ≤
      ut.regionBase.toNat + ut.regionSize ∧
    (untypedNextChild ut cap.freeIndex untypedId b).regionBase.toNat % SeLe4n.pageBytes = 0 ∧
    (untypedNextChild ut cap.freeIndex untypedId b).isDevice = ut.isDevice ∧
    (untypedNextChild ut cap.freeIndex untypedId b).parent = some untypedId ∧
    (untypedNextChild ut cap.freeIndex untypedId b).children = [] := by
  obtain ⟨ut₀, ut', cap₀, _, _, offset, _, hObj₀, _, _, hLk₀, _, hAlloc, _, _, _⟩ :=
    retypeFromUntyped_ok_decompose st st' authority untypedId childId _ _ hStep
  rw [hObj] at hObj₀
  have hEq : ut₀ = ut := by cases hObj₀; rfl
  subst hEq
  rw [hLk] at hLk₀
  have hEqC : cap₀ = cap := by cases hLk₀; rfl
  subst hEqC
  have hAligned := retypeFromUntyped_ok_pageAligned st st' authority untypedId childId
    _ _ ut₀ cap₀ hObj hLk rfl hStep
  have hCan := ((UntypedObject.allocate_some_iff ut₀ cap₀.freeIndex childId _ _).mp hAlloc).1
  simp only [UntypedObject.canAllocate, Bool.and_eq_true, decide_eq_true_eq] at hCan
  simp only [allocationBasePageAligned, beq_iff_eq] at hAligned
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
  · show ut₀.regionBase.toNat ≤ ut₀.regionBase.toNat + cap₀.freeIndex
    omega
  · show ut₀.regionBase.toNat + cap₀.freeIndex + 2 ^ b ≤ _
    omega
  · show (ut₀.regionBase.toNat + cap₀.freeIndex) % SeLe4n.pageBytes = 0
    simpa [SeLe4n.pageBytes] using hAligned

/-- **WS-BP BP7.1: the carve's payoff** — after a successful carve the store holds
the requested object at the child id, carved from the untyped the invoked
capability names, and the destination CNode holds the request's capability at
the destination slot.  With `untypedNextFrame_of_retype_ok` and
`untypedNextChild_of_retype_ok` this is the whole claim: the caller now holds a
capability to memory its untyped owned, and to nothing else. -/
theorem untypedRetypeObject_ok_carved
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (req : CarveRequest)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    ∃ (untypedId : SeLe4n.ObjId) (ut : UntypedObject) (utCap : Capability) (st1 : SystemState),
      st.objects[untypedId]? = some (.untyped ut) ∧
      cspaceLookupSlot src st = .ok (utCap, st) ∧
      retypeFromUntyped src untypedId childId (req.object untypedId childId ut utCap.freeIndex) req.size st
        = .ok ((), st1) ∧
      ((∀ cn, req.object untypedId childId ut utCap.freeIndex ≠ .cnode cn) →
        (∀ t, req.object untypedId childId ut utCap.freeIndex ≠ .tcb t) →
        st'.objects[childId]? = some (req.object untypedId childId ut utCap.freeIndex)) ∧
      (st'.objects[childId]?).map KernelObject.withoutLinks =
        some (req.object untypedId childId ut utCap.freeIndex).withoutLinks ∧
      ∃ cn cn' : CNode, st'.objects[dst.cnode]? = some (.cnode cn') ∧
        cn'.withoutLinks = (cn.insert dst.slot (req.capability childId)).withoutLinks := by
  obtain ⟨_, _, _, _, _, _, _, hD, _, _⟩ :=
    untypedRetypeObject_ok_writes src dst childId req st st' hStep
  obtain ⟨utCap, untypedId, ut, st1, st2, hLk, _, hUt, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hObjInv hStep
  have hObj : st.objects[untypedId]? = some (.untyped ut) :=
    (SystemState.getUntyped?_eq_some_iff st untypedId ut).mp hUt
  obtain ⟨_, ut', _, stL, stUt, _, stCh, _, _, _, hLkR, _, _, hStUt, hStCh, hIdx⟩ :=
    retypeFromUntyped_ok_decompose st st1 src untypedId childId _ _ hRt
  have hStL : stL = st := cspaceLookupSlot_ok_state_eq st src _ stL hLkR
  rw [hStL] at hStUt
  have hInvUt := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStUt
  have hInvCh := storeObject_preserves_objects_invExt _ _ _ _ hInvUt hStCh
  have hInv1 : st1.objects.invExt := by
    rw [hIdx]; exact setCapFreeIndex_preserves_objects_invExt hInvCh
  have hAtCh : stCh.objects[childId]? = some (req.object untypedId childId ut utCap.freeIndex) :=
    storeObject_objects_eq _ _ _ _ hInvUt hStCh
  have hNeSrc : childId ≠ src.cnode := by
    intro h
    have hFr := retypeFromUntyped_childId_fresh src untypedId childId _ _ st st1 hRt
    have hL : (SystemState.lookupSlotCap st src).isSome = true := by
      unfold cspaceLookupSlot at hLk
      cases hq : SystemState.lookupSlotCap st src with
      | none =>
        rw [hq] at hLk
        exfalso; revert hLk; dsimp only; split <;> simp
      | some _ => rfl
    have hC := cnodeInvoked_of_lookupSlotCap hL
    unfold cnodeInvoked SystemState.getCNode? at hC
    rw [← h] at hC
    cases hq : st.objects[childId]? with
    | none => rw [hq] at hC; cases hC
    | some _ => rw [hq] at hFr; cases hFr
  have hAt1 : st1.objects[childId]? = some (req.object untypedId childId ut utCap.freeIndex) := by
    rw [hIdx, setCapFreeIndex_objects_ne hInvCh hNeSrc]; exact hAtCh
  have hInvZ : (req.scrub st1 ut utCap.freeIndex).objects.invExt := by
    rw [CarveRequest.scrub_objects]; exact hInv1
  obtain ⟨cn, hCnPre, hCnPost⟩ := cspaceInsertSlot_objects_eq _ _ _ _ hInvZ hIns
  -- The destination CNode existed before the carve, and the child id held
  -- nothing (`retypeFromUntyped`'s collision guard): they are two keys.
  have hNe : childId ≠ dst.cnode := by
    intro h
    have hFr := retypeFromUntyped_childId_fresh src untypedId childId _ _ st st1 hRt
    unfold cspaceDstAdmitted SystemState.getCNode? at hD
    rw [← h] at hD
    cases hq : st.objects[childId]? with
    | none => rw [hq] at hD; cases hD
    | some _ => rw [hq] at hFr; cases hFr
  have hAt2 : st2.objects[childId]? = some (req.object untypedId childId ut utCap.freeIndex) := by
    rw [cspaceInsertSlot_preserves_objects_ne _ _ _ _ _ hNe hInvZ hIns,
      CarveRequest.scrub_objects]; exact hAt1
  have hR := (SystemState.cdtAddChild_agreeObjects
    (cspaceInsertSlot_preserves_objects_invExt _ _ _ _ hInvZ hIns) src dst .retype).1
  obtain ⟨cn', hC, hw⟩ := hR.cnode_fwd hCnPost
  have hW : ((st2.cdtAddChild src dst .retype).objects[childId]?).map KernelObject.withoutLinks =
      some (req.object untypedId childId ut utCap.freeIndex).withoutLinks := by
    rw [(hR childId).map_withoutLinks, hAt2]; rfl
  exact ⟨untypedId, ut, utCap, st1, hObj, hLk, hRt, fun hn ht => hR.obj_fwd hAt2 hn ht, hW, cn, cn',
    hC, hw⟩

/-- **WS-BP BP7.1: a frame carve's payoff** — the frame is the page at the
invoked capability's free index, inside the untyped, on a page boundary and of its memory
kind, and the destination holds the frame capability. -/
theorem untypedRetypeObject_ok_frame
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst .frame st = .ok ((), st')) :
    ∃ (untypedId : SeLe4n.ObjId) (ut : UntypedObject) (idx : Nat),
      st.objects[untypedId]? = some (.untyped ut) ∧
      st'.getFrame? childId = some (untypedNextFrame ut idx) ∧
      ut.regionBase.toNat ≤ (untypedNextFrame ut idx).base.toNat ∧
      (untypedNextFrame ut idx).base.toNat + SeLe4n.pageBytes ≤
        ut.regionBase.toNat + ut.regionSize ∧
      (untypedNextFrame ut idx).wellFormed ∧
      (untypedNextFrame ut idx).isDevice = ut.isDevice ∧
      ∃ cn cn' : CNode, st'.objects[dst.cnode]? = some (.cnode cn') ∧
        cn'.withoutLinks = (cn.insert dst.slot (frameCapability childId)).withoutLinks := by
  obtain ⟨untypedId, ut, utCap, st1, hObj, hLk, hRt, hAt, -, hCn⟩ :=
    untypedRetypeObject_ok_carved src dst childId .frame st st' hObjInv hStep
  obtain ⟨hLo, hHi, hWf, hDev⟩ := untypedNextFrame_of_retype_ok st st1 src untypedId childId
    ut utCap hObj hLk hRt
  refine ⟨untypedId, ut, utCap.freeIndex, hObj, ?_, hLo, hHi, hWf, hDev, hCn⟩
  simp only [SystemState.getFrame?, hAt (by intro _ h; simp [CarveRequest.object] at h)
      (by intro _ h; simp [CarveRequest.object] at h),
    CarveRequest.object]

/-- **WS-BP BP7.1 slice 4 (`v0.36.8`): a child-untyped carve's payoff** — the
store holds, at the child id, an untyped whose region lies inside its parent's
on a page boundary, of the parent's memory kind, with the parent stamped and
nothing yet carved from it; and the destination holds a capability carrying
`.retype` to it, so the caller can carve from the child and reset it. -/
theorem untypedRetypeObject_ok_untyped
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (b : Nat) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst (.untyped b) st = .ok ((), st')) :
    ∃ (untypedId : SeLe4n.ObjId) (ut : UntypedObject) (idx : Nat),
      st.objects[untypedId]? = some (.untyped ut) ∧
      st'.objects[childId]? = some (.untyped (untypedNextChild ut idx untypedId b)) ∧
      ut.regionBase.toNat ≤ (untypedNextChild ut idx untypedId b).regionBase.toNat ∧
      (untypedNextChild ut idx untypedId b).regionBase.toNat + 2 ^ b ≤
        ut.regionBase.toNat + ut.regionSize ∧
      (untypedNextChild ut idx untypedId b).regionBase.toNat % SeLe4n.pageBytes = 0 ∧
      (untypedNextChild ut idx untypedId b).isDevice = ut.isDevice ∧
      (untypedNextChild ut idx untypedId b).parent = some untypedId ∧
      ∃ cn cn' : CNode, st'.objects[dst.cnode]? = some (.cnode cn') ∧
        cn'.withoutLinks = (cn.insert dst.slot (untypedCapability childId)).withoutLinks := by
  obtain ⟨untypedId, ut, utCap, st1, hObj, hLk, hRt, hAt, -, hCn⟩ :=
    untypedRetypeObject_ok_carved src dst childId (.untyped b) st st' hObjInv hStep
  obtain ⟨hLo, hHi, hAl, hDev, hPar, -⟩ :=
    untypedNextChild_of_retype_ok st st1 src untypedId childId ut utCap b hObj hLk hRt
  exact ⟨untypedId, ut, utCap.freeIndex, hObj, hAt (by intro _ h; simp [CarveRequest.object] at h)
      (by intro _ h; simp [CarveRequest.object] at h),
    hLo, hHi, hAl, hDev, hPar, hCn⟩

/-- **WS-BP BP7.1 slice 4b (`v0.36.10`): a VSpace-root carve's payoff** — the
store holds, at the child id, a root with no mappings, registered under an ASID
that was non-zero, in range and **free in the ASID table before the carve**, and
whose table base is a page inside the untyped, on a page boundary, of RAM; and
the destination holds a read/write capability to it.  This is what the in-place
retype could not say (`v0.36.9`): the root it built at ASID `0` took an entry
another root held. -/
theorem untypedRetypeObject_ok_vspaceRoot
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (asid : SeLe4n.ASID)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst (.vspaceRoot asid) st = .ok ((), st')) :
    ∃ (untypedId : SeLe4n.ObjId) (ut : UntypedObject) (idx : Nat),
      st.objects[untypedId]? = some (.untyped ut) ∧
      st'.objects[childId]? = some (.vspaceRoot (untypedNextVSpaceRoot ut idx asid)) ∧
      asid.toNat ≠ 0 ∧ asid.toNat < st.machine.maxASID ∧ st.asidTable[asid]? = none ∧
      (untypedNextVSpaceRoot ut idx asid).tableBase = some (untypedNextFrame ut idx).base ∧
      ut.regionBase.toNat ≤ (untypedNextFrame ut idx).base.toNat ∧
      (untypedNextFrame ut idx).base.toNat + SeLe4n.pageBytes ≤
        ut.regionBase.toNat + ut.regionSize ∧
      (untypedNextFrame ut idx).base.toNat % SeLe4n.pageBytes = 0 ∧
      ut.isDevice = false ∧
      ∃ cn cn' : CNode, st'.objects[dst.cnode]? = some (.cnode cn') ∧
        cn'.withoutLinks = (cn.insert dst.slot (vspaceRootCapability childId)).withoutLinks := by
  have hAdm := untypedRetypeObject_ok_admissible src dst childId _ st st' hStep
  simp only [CarveRequest.admissible, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, Option.isNone_iff_eq_none] at hAdm
  obtain ⟨⟨hNz, hLt⟩, hFree⟩ := hAdm
  obtain ⟨untypedId, ut, utCap, st1, hObj, hLk, hRt, hAt, -, hCn⟩ :=
    untypedRetypeObject_ok_carved src dst childId (.vspaceRoot asid) st st' hObjInv hStep
  obtain ⟨hTb, hLo, hHi, hAl, hDev⟩ :=
    untypedNextVSpaceRoot_of_retype_ok st st1 src untypedId childId ut utCap asid hObj hLk hRt
  exact ⟨untypedId, ut, utCap.freeIndex, hObj, hAt (by intro _ h; simp [CarveRequest.object] at h)
      (by intro _ h; simp [CarveRequest.object] at h),
    hNz, hLt, hFree, hTb, hLo, hHi, hAl, hDev, hCn⟩

/-! ### WS-ZA ZA5.4 part 14: the kernel objects a carve makes

Each payoff names the object the store holds at the child id after a successful
carve — the object seL4's `createObject` makes for that type — and the
capability, with every right, that the destination slot now holds. -/

/-- A carve's slot write, for a kernel-object request: the destination CNode
holds the all-rights capability to the child. -/
theorem untypedRetypeObject_ok_kernelCapability
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (req : CarveRequest)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st'))
    (hKernel : req.capability childId = kernelObjectCapability childId) :
    ∃ cn cn' : CNode, st'.objects[dst.cnode]? = some (.cnode cn') ∧
      cn'.withoutLinks = (cn.insert dst.slot (kernelObjectCapability childId)).withoutLinks := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hCn⟩ :=
    untypedRetypeObject_ok_carved src dst childId req st st' hObjInv hStep
  rw [hKernel] at hCn; exact hCn

/-- **A carved TCB** is the thread seL4's `createObject` makes for
`seL4_TCBObject`: inactive, not blocked in IPC, at priority and maximum
controlled priority `0`, in the domain and on the core the request names, bound
to no scheduling context or notification, queued on no run queue and with both
space slots empty.  Its space-slot links are the only part the derivation edge's
write may touch, so the payoff reads the thread through them. -/
theorem untypedRetypeObject_ok_tcb
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (dom : SeLe4n.DomainId)
    (core : SeLe4n.Kernel.Concurrency.CoreId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst (.tcb dom core) st = .ok ((), st')) :
    ∃ tcb : TCB, st'.objects[childId]? = some (.tcb tcb) ∧
      tcb.withoutLinks = (carvedTcb childId dom core).withoutLinks ∧
      tcb.tid = SeLe4n.ThreadId.ofObjId childId ∧
      tcb.threadState = .Inactive ∧ tcb.ipcState = .ready ∧
      tcb.priority = SeLe4n.Priority.ofNat 0 ∧
      tcb.maxControlledPriority = SeLe4n.Priority.ofNat 0 ∧
      tcb.domain = dom ∧ tcb.cpuAffinity = some core ∧
      tcb.schedContextBinding = .unbound ∧ tcb.boundNotification = none ∧
      tcb.runCoreCode = 0 ∧ tcb.pendingMessage = none ∧
      tcb.spaceCells = #v[none, none] := by
  obtain ⟨_, _, _, _, _, _, _, _, hW, -⟩ :=
    untypedRetypeObject_ok_carved src dst childId (.tcb dom core) st st' hObjInv hStep
  cases hO : st'.objects[childId]? with
  | none => rw [hO] at hW; cases hW
  | some o =>
    rw [hO] at hW
    cases o <;> simp [CarveRequest.object, KernelObject.withoutLinks] at hW
    rename_i tcb
    refine ⟨tcb, rfl, hW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.tid) hW
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.threadState) hW
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.ipcState) hW
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.priority) hW
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.maxControlledPriority) hW
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.domain) hW
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.cpuAffinity) hW
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.schedContextBinding) hW
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.boundNotification) hW
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.runCoreCode) hW
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.pendingMessage) hW
    · exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.spaceCells) hW

/-- A carved thread is queued on no core. -/
theorem untypedRetypeObject_ok_tcb_notQueued
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (dom : SeLe4n.DomainId)
    (core : SeLe4n.Kernel.Concurrency.CoreId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst (.tcb dom core) st = .ok ((), st'))
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    st'.queuedOn c (SeLe4n.ThreadId.ofObjId childId) = false := by
  obtain ⟨tcb, hO, -, -, -, -, -, -, -, -, -, -, hRc, -⟩ :=
    untypedRetypeObject_ok_tcb src dst childId dom core st st' hObjInv hStep
  unfold SystemState.queuedOn SystemState.getTcb?
  rw [SeLe4n.ThreadId.toObjId_ofObjId, hO]
  simp [hRc]

/-- **A carved endpoint** is idle: both its queues are empty. -/
theorem untypedRetypeObject_ok_endpoint
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst .endpoint st = .ok ((), st')) :
    st'.objects[childId]? = some (.endpoint (Endpoint.ofQueues {} {})) ∧
      (Endpoint.ofQueues {} {}).sendQ = {} ∧ (Endpoint.ofQueues {} {}).receiveQ = {} := by
  obtain ⟨_, _, _, _, _, _, _, hAt, -, -⟩ :=
    untypedRetypeObject_ok_carved src dst childId .endpoint st st' hObjInv hStep
  exact ⟨hAt (by intro _ h; simp [CarveRequest.object] at h)
    (by intro _ h; simp [CarveRequest.object] at h), rfl, rfl⟩

/-- **A carved notification** is idle: no thread waits on it and no badge is
pending. -/
theorem untypedRetypeObject_ok_notification
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst .notification st = .ok ((), st')) :
    st'.objects[childId]? = some (.notification { state := .idle }) := by
  obtain ⟨_, _, _, _, _, _, _, hAt, -, -⟩ :=
    untypedRetypeObject_ok_carved src dst childId .notification st st' hObjInv hStep
  exact hAt (by intro _ h; simp [CarveRequest.object] at h)
    (by intro _ h; simp [CarveRequest.object] at h)

/-- **A carved CNode** has `2 ^ radixBits` slots, every one empty, and no guard. -/
theorem untypedRetypeObject_ok_cnode
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (r : Nat) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst (.cnode r) st = .ok ((), st')) :
    ∃ cn : CNode, st'.objects[childId]? = some (.cnode cn) ∧
      cn.withoutLinks = (carvedCNode r).withoutLinks ∧
      cn.radixWidth = (carvedCNode r).radixWidth ∧ cn.guardWidth = (carvedCNode r).guardWidth ∧
      ∀ s, cn.lookup s = (carvedCNode r).lookup s := by
  obtain ⟨_, _, _, _, _, _, _, _, hW, -⟩ :=
    untypedRetypeObject_ok_carved src dst childId (.cnode r) st st' hObjInv hStep
  cases hO : st'.objects[childId]? with
  | none => rw [hO] at hW; cases hW
  | some o =>
    rw [hO] at hW
    cases o <;> simp [CarveRequest.object, KernelObject.withoutLinks] at hW
    rename_i cn
    exact ⟨cn, rfl, hW, CNode.proj_eq_of_withoutLinks_eq CNode.radixWidth hW,
      CNode.proj_eq_of_withoutLinks_eq CNode.guardWidth hW,
      fun s => CNode.proj_eq_of_withoutLinks_eq (fun c => c.lookup s) hW⟩

/-- **A carved reply** answers no caller and is linked to no other reply. -/
theorem untypedRetypeObject_ok_reply
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst .reply st = .ok ((), st')) :
    st'.objects[childId]? =
        some (.reply (SeLe4n.Kernel.Reply.empty (SeLe4n.ReplyId.ofObjId childId))) ∧
      (SeLe4n.Kernel.Reply.empty (SeLe4n.ReplyId.ofObjId childId)).caller = none ∧
      (SeLe4n.Kernel.Reply.empty (SeLe4n.ReplyId.ofObjId childId)).prev = none ∧
      (SeLe4n.Kernel.Reply.empty (SeLe4n.ReplyId.ofObjId childId)).next = none := by
  obtain ⟨_, _, _, _, _, _, _, hAt, -, -⟩ :=
    untypedRetypeObject_ok_carved src dst childId .reply st st' hObjInv hStep
  exact ⟨hAt (by intro _ h; simp [CarveRequest.object] at h)
    (by intro _ h; simp [CarveRequest.object] at h), rfl, rfl, rfl⟩

/-- **A carved scheduling context** is bound to no thread and has a zero budget:
seL4's `createObject` leaves a scheduling context unconfigured until
`seL4_SchedControl_Configure`. -/
theorem untypedRetypeObject_ok_schedContext
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (b : Nat) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst (.schedContext b) st = .ok ((), st')) :
    st'.objects[childId]? = some (.schedContext
        (SeLe4n.Kernel.SchedContext.empty (SeLe4n.SchedContextId.ofObjId childId))) ∧
      (SeLe4n.Kernel.SchedContext.empty (SeLe4n.SchedContextId.ofObjId childId)).boundThread
        = none ∧
      (SeLe4n.Kernel.SchedContext.empty (SeLe4n.SchedContextId.ofObjId childId)).budget
        = SeLe4n.Kernel.Budget.zero := by
  obtain ⟨_, _, _, _, _, _, _, hAt, -, -⟩ :=
    untypedRetypeObject_ok_carved src dst childId (.schedContext b) st st' hObjInv hStep
  exact ⟨hAt (by intro _ h; simp [CarveRequest.object] at h)
    (by intro _ h; simp [CarveRequest.object] at h), rfl, rfl⟩



end SeLe4n.Kernel
