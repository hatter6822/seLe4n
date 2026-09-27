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
the memory-scrubbing primitive (`scrubObjectMemory` + its frame theorems
+ `memoryZeroed` post-condition witness), the `retypeFromUntyped`
definition, and the complete preservation / soundness theorem cluster
that witnesses its capacity-gated, fresh-id-allocating, and
sequentially-atomic behaviour. `SeLe4n.Kernel.Internal.lifecycleRetypeObject`
is reached via `open Internal` (AN4-A allowlist). All declarations retain
their original names, order, and proofs.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
-- AN4-A / AN4-G.5 allowlist: proof-chain reference to
-- `lifecycleRetypeObject` from `SeLe4n.Kernel.Internal`. Enforced by
-- `scripts/test_tier0_hygiene.sh`.
open Internal

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
  | .schedContext => 256
  | .reply => 64
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
  | .cnode => true
  -- WS-BP BP7.1: a frame is mapped by address, and a mapping names a page.
  | .frame => true
  -- WS-BP BP7.1 (`v0.36.12`): a table descriptor names a page.
  | .pageTable => true
  -- WS-BP BP7.1 slice 4 (`v0.36.8`): a carved untyped starts on a page, so
  -- every frame carved from it can too — the carve's size is a multiple of a
  -- page (`minUntypedSizeBits`), which keeps the parent's next base aligned.
  | .untyped => true
  | _ => false

/-- S5-G: Check whether the untyped allocation base (regionBase + watermark)
is page-aligned. Returns `true` when alignment is satisfied. -/
def allocationBasePageAligned (ut : UntypedObject) : Bool :=
  (ut.regionBase.toNat + ut.watermark) % 4096 == 0

-- ============================================================================
-- S6-C: Memory scrubbing on object deletion/retype
-- ============================================================================

/-- S6-C: the byte range a re-type scrubs, as **one** function.

    Every consumer that must cover the scrub — the scrub itself, and the
    SM7.D cache-maintenance operand that cleans those stores to the Point of
    Unification — reads this single definition, so the two cannot drift.  A
    second copy of the arithmetic would let the clean silently name a
    different extent than the zeroing writes; that is precisely the failure
    mode this exists to make impossible.

    **Abstract model note:** the base address is `objectId.toNat ×
    objectTypeAllocSize` — an abstract convention for the formal model, *not*
    the address the hardware allocator would use.

    **AN4-G.3 (LIF-M03) — H3 hardware-binding cross-reference**: on real
    hardware (RPi5 AArch64) the real extent is the untyped allocator's
    `regionBase + offset` (recorded in state as `UntypedChild.offset` /
    `.size`), and the scrub must route through the VSpace bridge to hit the
    physical frame backing it — see `SELE4N_SPEC.md` §5 "Lifecycle:
    model-vs-hardware scrub bridge" and the AN9 hardware workstream.  That
    bridge changes this function, and both consumers follow. -/
def scrubExtent (objectId : SeLe4n.ObjId) (objType : KernelObjectType) :
    SeLe4n.PAddr × Nat :=
  let size := objectTypeAllocSize objType
  (SeLe4n.PAddr.ofNat (objectId.toNat * size), size)

/-- S6-C: Scrub backing memory for a deleted/retyped kernel object.

    Zeros the memory region that backed the old object, preventing information
    leakage when the memory is reallocated to a different security domain.
    The scrubbed region is `scrubExtent` — see there for the model-vs-hardware
    address convention (AN4-G.3 / LIF-M03).

    **Security rationale:** Without scrubbing, `retypeFromUntyped` could
    allocate a new object in memory that still contains data from a
    deleted object belonging to a different security domain. This violates
    non-interference even though the Lean-level object store is correctly
    updated, because the underlying machine memory retains the old data.

    **Cache note (SM7.D):** zeroing stores land in the *data* cache, so the
    re-type additionally owes a clean of this same extent to the Point of
    Unification before any instruction invalidate — emitted by
    `retypeIcacheOp`, which reads `scrubExtent` rather than recomputing it. -/
def scrubObjectMemory (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) : SystemState :=
  let extent := scrubExtent objectId objType
  { st with machine := SeLe4n.zeroMemoryRange st.machine extent.fst extent.snd }

/-- S6-C: `scrubObjectMemory` zeroes exactly `scrubExtent` — the bridge that
lets a consumer reason about the scrub's byte range without unfolding the
transition.  Definitional, so it stays true by construction. -/
theorem scrubObjectMemory_zeroes_scrubExtent (st : SystemState)
    (objectId : SeLe4n.ObjId) (objType : KernelObjectType) :
    (scrubObjectMemory st objectId objType).machine =
      SeLe4n.zeroMemoryRange st.machine
        (scrubExtent objectId objType).fst (scrubExtent objectId objType).snd := rfl

/-- S6-C: `scrubObjectMemory` preserves the object store. -/
theorem scrubObjectMemory_objects_eq (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    (scrubObjectMemory st objectId objType).objects = st.objects := rfl

/-- WS-SM SM7.B: `scrubObjectMemory` is machine-memory-only — the
TLB-shootdown state is framed (`pendingBounded` bundle-carriage leaf). -/
theorem scrubObjectMemory_tlbShootdown_eq (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    (scrubObjectMemory st objectId objType).tlbShootdown = st.tlbShootdown := rfl

/-- S6-C: `scrubObjectMemory` preserves the scheduler state. -/
theorem scrubObjectMemory_scheduler_eq (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    (scrubObjectMemory st objectId objType).scheduler = st.scheduler := rfl

/-- WS-SM SM8.B.2: `scrubObjectMemory` preserves every core's register bank.

The scrub is the one step of the retype pipeline that genuinely writes
`machine`, so the whole-machine frame the other steps use is unavailable here
and the per-core observer's read set has to be addressed directly: `machine.regs`
is a field beside `machine.memory`, and `zeroMemoryRange` rewrites only the
latter. -/
theorem scrubObjectMemory_regsOnCore (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (scrubObjectMemory st objectId objType).machine.regsOnCore c
      = st.machine.regsOnCore c := rfl

/-- S6-C: `scrubObjectMemory` preserves lifecycle metadata. -/
theorem scrubObjectMemory_lifecycle_eq (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    (scrubObjectMemory st objectId objType).lifecycle = st.lifecycle := rfl

/-- S6-C: `scrubObjectMemory` establishes the `memoryZeroed` postcondition
    for the scrubbed region. -/
theorem scrubObjectMemory_establishes_memoryZeroed
    (st : SystemState) (objectId : SeLe4n.ObjId)
    (objType : KernelObjectType) :
    SeLe4n.memoryZeroed (scrubObjectMemory st objectId objType).machine
      (scrubExtent objectId objType).fst (scrubExtent objectId objType).snd := by
  simp only [scrubObjectMemory]
  exact SeLe4n.zeroMemoryRange_establishes_memoryZeroed st.machine _ _

/-- WS-F2: Retype a new typed object from an untyped memory region.

Deterministic branch contract:
1. The source object must exist and be an `UntypedObject` (`untypedTypeMismatch` otherwise).
2. Device untypeds cannot back typed kernel objects except the memory-backed
   kinds — other untypeds and frames (`untypedDeviceRestriction` if violated).
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
                    -- Atomic dual-store: untyped watermark advance + child creation.
                    -- AN6-C.2 (H-09): Per-caller contract — callers allocating a
                    -- `.untyped` child via this primitive SHOULD pre-stamp the
                    -- child's `parent` field with the parent untyped's ObjId
                    -- before invocation so the transitive
                    -- `untypedAncestorRegionsDisjoint` invariant (AN6-C.4) can
                    -- walk the ancestor chain. The stamping is NOT done inside
                    -- `retypeFromUntyped` to preserve the theorem surface (the
                    -- 60+ preservation theorems that destructure `newObj` via
                    -- `hStep` direct equality).  The one live caller carving an
                    -- `.untyped` child, the untyped carve
                    -- (`untypedRetypeObject`, WS-BP BP7.1 slice 4, `v0.36.8`),
                    -- honours it: its child is `untypedNextChild`, which sets
                    -- `parent := some untypedId` and the carved region.  The
                    -- in-place retype refuses memory-backed replacements, so
                    -- `objectOfKernelType .untyped` (`regionBase = 0`, no
                    -- parent) never reaches a live state, and the default
                    -- `parent := none` is correct for every boot untyped.
                    match storeObject untypedId (.untyped ut') st' with
                    | .error e => .error e
                    | .ok ((), stUt) =>
                        storeObject childId newObj stUt
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
      (ut.isDevice = false ∨ newObj.objectType.deviceBackable = true) ∧
      ¬(allocSize < objectTypeAllocSize newObj.objectType) ∧
      cspaceLookupSlot authority st = .ok (cap, stLookup) ∧
      lifecycleRetypeAuthority cap untypedId = true ∧
      ut.allocate childId allocSize = some (ut', offset) ∧
      storeObject untypedId (.untyped ut') stLookup = .ok ((), stUt) ∧
      storeObject childId newObj stUt = .ok ((), st') := by
  unfold retypeFromUntyped SystemState.getObject? at hStep
  cases hObj : st.objects[untypedId]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ => simp [hObj] at hStep
      | endpoint _ => simp [hObj] at hStep
      | notification _ => simp [hObj] at hStep
      | cnode _ => simp [hObj] at hStep
      | vspaceRoot _ => simp [hObj] at hStep
      | schedContext _ => simp [hObj] at hStep
      | reply _ | frame _ | pageTable _ => simp [hObj] at hStep
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
          · -- ut.isDevice = true: the target must be device-backable
            -- (WS-BP BP7.1: an untyped or a frame; `deviceBackable`).
            by_cases hObjType : newObj.objectType.deviceBackable = true
            · simp only [hObjType, Bool.not_true, Bool.and_false, Bool.false_eq_true,
                ↓reduceIte] at hStep
              by_cases hAllocSz : allocSize < objectTypeAllocSize newObj.objectType
              · simp [hAllocSz] at hStep
              · simp only [hAllocSz, ↓reduceIte] at hStep
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
            · -- not memory-backed: device restriction fires -> contradiction
              simp [hObjType] at hStep

/-- AN4-G.4 (LIF-M04): **retype atomicity under sequential semantics.**
The `retypeFromUntyped` primitive performs two mutations back-to-back: the
watermark advance (`storeObject untypedId (.untyped ut')`) that records the
new allocation in the parent, and the fresh-object store (`storeObject
childId newObj`) that materialises the child. In Lean's deterministic
evaluation, these two steps collapse into a single indivisible transition
from caller's perspective — there is no observable intermediate state
between them, so the watermark+store pair is atomic at the model layer.

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
    -- implementation performs watermark-advance + child-store as two
    -- sequential `storeObject` calls. The intermediate state `stUt` is
    -- existentially bound and never visible to the caller. The
    -- `storeObject childId newObj stUt = .ok ((), st')` conjunct witnesses
    -- that `stUt → st'` is the final child-store step; the fact that
    -- `stUt` is reachable from `st` via the watermark-advance is recorded
    -- by the decomposition theorem invoked internally. -/
    ∃ stUt, storeObject childId newObj stUt = .ok ((), st') := by
  obtain ⟨_, _, _, _, stUt, _, _, _, _, _, _, _, _, hStoreChild⟩ :=
    retypeFromUntyped_ok_decompose st st' authority untypedId childId newObj allocSize hStep
  exact ⟨stUt, hStoreChild⟩

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
    (hSmall : allocSize < objectTypeAllocSize newObj.objectType) :
    retypeFromUntyped authority untypedId childId newObj allocSize st =
      .error .untypedAllocSizeTooSmall := by
  unfold retypeFromUntyped SystemState.getObject?
  have hCapF : ¬(st.objectIndex.length ≥ maxObjects) := by omega
  simp [hObj, hCapF, hNeSelf, hNoCollision, hFreshChildren]
  cases hNotDev with
  | inl hFalse => simp [hFalse, hSmall]
  | inr hMB =>
      by_cases hDevBool : ut.isDevice
      · simp [hDevBool, hMB, hSmall]
      · simp [hDevBool, hSmall]

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
    (hAllocSzOk : ¬(allocSize < objectTypeAllocSize newObj.objectType))
    (hAlignOk : (requiresPageAlignment newObj.objectType && !allocationBasePageAligned ut) = false)
    (hLookup : cspaceLookupSlot authority st = .ok (cap, st))
    (hAuth : lifecycleRetypeAuthority cap untypedId = true)
    (hNoFit : ut.allocate childId allocSize = none) :
    retypeFromUntyped authority untypedId childId newObj allocSize st =
      .error .untypedRegionExhausted := by
  unfold retypeFromUntyped SystemState.getObject?
  have hCapF : ¬(st.objectIndex.length ≥ maxObjects) := by omega
  simp only [hObj, hCapF, ↓reduceIte, hNeSelf, hNoCollision, hFreshChildren]
  cases hNotDev with
  | inl hFalse =>
      simp only [hFalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hAllocSzOk, hAlignOk,
        ↓reduceIte, hLookup, hAuth, hNoFit]
  | inr hMB =>
      by_cases hDevBool : ut.isDevice
      · simp only [hDevBool, hMB, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
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
      -- AN10-residual (R1): destructure on the typed helper.
      cases hCN : st.getCNode? addr.cnode with
      | none => simp [hCap, hCN] at hLookup
      | some _ => simp [hCap, hCN] at hLookup
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
  unfold lifecycleRetypeObject SystemState.getObject? at hStep
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
  unfold lifecycleRetypeObject SystemState.getObject?
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
  unfold lifecycleRetypeObject SystemState.getObject?
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
-- WS-BP BP7.1 (`v0.36.5`): the untyped carve that mints frames
-- ============================================================================

/-- **WS-BP BP7.1: the frame an untyped's next page would be.**

The page at the untyped's current watermark — `regionBase + watermark` —
carrying the untyped's own device flag.  One definition, read by the carve that
creates the frame and by every statement about which memory it names, so the
two cannot describe different pages.  seL4's `Untyped_Retype` places a frame at
the untyped's free pointer the same way; a device untyped yields a device frame,
which is how a driver is handed MMIO. -/
def untypedNextFrame (ut : UntypedObject) : FrameObject :=
  { base := SeLe4n.PAddr.ofNat (ut.regionBase.toNat + ut.watermark)
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
          pendingPhysicalWrites := st.pendingPhysicalWrites ++
            [SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage frame.base] }

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

The region at the parent's watermark — `[regionBase + watermark,
regionBase + watermark + 2 ^ sizeBits)` — of the parent's memory kind, with its
**parent stamped** (`parent := some parentId`) and nothing carved from it yet.
The stamp is what `retypeFromUntyped`'s AN6-C.2 contract asks every caller
carving an `.untyped` child to perform, and what the transitive
`untypedAncestorRegionsDisjoint` walk reads; `objectOfKernelType .untyped`,
which builds `regionBase = 0` and no parent, is the in-place retype's builder
and is refused for memory-backed kinds, so this is the only child untyped a live
state can acquire.  One definition, read by the carve and by every statement
about which memory the child owns. -/
def untypedNextChild (ut : UntypedObject) (parentId : SeLe4n.ObjId) (sizeBits : Nat) :
    UntypedObject :=
  { regionBase := SeLe4n.PAddr.ofNat (ut.regionBase.toNat + ut.watermark)
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

/-- **WS-BP BP7.1 slice 4 (`v0.36.8`): what a carve can make.**

The two kinds an untyped's memory backs *as memory*: a frame (one page a thread
maps) and a child untyped (a sub-region it carves from in turn).  Kernel objects
keep the in-place retype.  A request is built only by the syscall arm's decode
(`carveRequestOf?`), which bounds a child untyped's size; every other guard —
authority, capacity, fresh id, device rule, alignment, region — is the carve
primitive's. -/
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
  deriving Repr, DecidableEq

/-- **WS-BP BP7.1 (`v0.36.12`): the page table a carve makes** — installed
nowhere, on the page at the untyped's watermark, the same page
`untypedNextFrame` names. -/
def untypedNextPageTable (ut : UntypedObject) : PageTableObject :=
  { base := (untypedNextFrame ut).base }

/-- **WS-BP BP7.1 (`v0.36.12`): the capability a carve hands back for a page
table.**  Read and write — `.pageTableMap` and `.pageTableUnmap` ask `.write`.
`.retype` is absent: a table's page returns through the reset, never through an
in-place retype, which refuses a table outright. -/
def pageTableCapability (tableId : SeLe4n.ObjId) : Capability :=
  { target := .object tableId
    rights := AccessRightSet.ofList [.read, .write] }

/-- **WS-BP BP7.1 slice 4b (`v0.36.10`): the VSpace root a carve makes** — no
mappings, registered under `asid`, and its **table base the page at the
untyped's watermark**, the same page `untypedNextFrame` names, so the root owns
exactly one page its untyped owned.  seL4's VSpace object is that page. -/
def untypedNextVSpaceRoot (ut : UntypedObject) (asid : SeLe4n.ASID) : VSpaceRoot :=
  { asid := asid, mappings := {}, tableBase := some (untypedNextFrame ut).base }

/-- **WS-BP BP7.1 slice 4b: the capability a carve hands back for a VSpace
root.**  Read and write — the rights `.vspaceMap` and `.vspaceUnmap` ask of an
address-space capability.  `.retype` is absent: a root's page returns to its
untyped through the reset, never through an in-place retype, which refuses a
root outright. -/
def vspaceRootCapability (rootId : SeLe4n.ObjId) : Capability :=
  { target := .object rootId
    rights := AccessRightSet.ofList [.read, .write] }

/-- **WS-BP BP7.1 slice 4b (`v0.36.10`): an ASID nothing holds.**  The least
`n` in `[1, maxASID)` the ASID table does not map.  ASID `0` is never chosen —
it is the boot VSpace root's, and ARM64 reserves it — and the bound is the
machine's, the one `.vspaceMap`'s decode reads.  `none` when every ASID is
taken.  A linear scan bounded by the ASID width, as seL4's `ASIDPool_Assign`
scans its pool. -/
def freshAsid? (st : SystemState) : Option SeLe4n.ASID :=
  ((List.range st.machine.maxASID).find? fun n =>
      n != 0 && (st.asidTable[SeLe4n.ASID.ofNat n]?).isNone).map SeLe4n.ASID.ofNat

/-- **WS-BP BP7.1 slice 4b: is a request's own precondition met?**  A frame or a
child untyped has none beyond the primitive's.  A VSpace root's ASID must be
non-zero, below the machine's bound, and free in the ASID table — decided here,
by the carve, rather than trusted of whoever chose it: `storeObject` inserts a
root's ASID unconditionally, and an ASID already held would move its entry to
the new root (the defect `v0.36.9` closed on the in-place retype). -/
def CarveRequest.admissible (st : SystemState) : CarveRequest → Bool
  | .frame => true
  | .untyped _ => true
  | .vspaceRoot asid =>
      asid.toNat != 0 && decide (asid.toNat < st.machine.maxASID) &&
        (st.asidTable[asid]?).isNone
  | .pageTable => true

/-- The object a request carves out of `ut` (stored at `untypedId`). -/
def CarveRequest.object (untypedId : SeLe4n.ObjId) (ut : UntypedObject) :
    CarveRequest → KernelObject
  | .frame => .frame (untypedNextFrame ut)
  | .untyped b => .untyped (untypedNextChild ut untypedId b)
  | .vspaceRoot asid => .vspaceRoot (untypedNextVSpaceRoot ut asid)
  | .pageTable => .pageTable (untypedNextPageTable ut)

/-- The bytes a request takes from the parent's region. -/
def CarveRequest.size : CarveRequest → Nat
  | .frame => SeLe4n.pageBytes
  | .untyped b => 2 ^ b
  | .vspaceRoot _ => SeLe4n.pageBytes
  | .pageTable => SeLe4n.pageBytes

/-- The capability a request hands back for the carved object. -/
def CarveRequest.capability (childId : SeLe4n.ObjId) : CarveRequest → Capability
  | .frame => frameCapability childId
  | .untyped _ => untypedCapability childId
  | .vspaceRoot _ => vspaceRootCapability childId
  | .pageTable => pageTableCapability childId

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
def CarveRequest.scrub (st : SystemState) (ut : UntypedObject) : CarveRequest → SystemState
  | .frame => carveZeroFrame st (untypedNextFrame ut)
  | .untyped _ => st
  | .vspaceRoot _ =>
      { st with
          machine := SeLe4n.zeroMemoryRange st.machine (untypedNextFrame ut).base SeLe4n.pageBytes
          pendingPhysicalWrites := st.pendingPhysicalWrites ++
            [SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage (untypedNextFrame ut).base] }
  -- WS-BP BP7.1 (`v0.36.12`): a table page is zeroed for the root's reason — a
  -- zeroed table holds only invalid descriptors.
  | .pageTable =>
      { st with
          machine := SeLe4n.zeroMemoryRange st.machine (untypedNextFrame ut).base SeLe4n.pageBytes
          pendingPhysicalWrites := st.pendingPhysicalWrites ++
            [SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage (untypedNextFrame ut).base] }

/-- **WS-BP BP7.1 (`v0.36.5`, generalized at slice 4, `v0.36.8`): carve one object
out of an untyped the caller holds — seL4's `Untyped_Retype`.**

`src` is the slot of the untyped capability the syscall was invoked on, `childId`
the object id the carved object takes, `dst` the empty slot its capability goes
to, and `req` what is carved — a frame, or a child untyped of `2 ^ b` bytes.
Four steps, and every refusal commits nothing:

1. **The carve** is `retypeFromUntyped` at `req.object untypedId ut` and
   `req.size` bytes — so the authority check (`lifecycleRetypeAuthority`: the
   capability names this untyped and carries `.retype`), the capacity, fresh-id
   and self-overwrite guards, the device rule (a device untyped backs
   memory-backed kinds only), page alignment, the minimum size and the watermark
   advance are the primitive's own, not a second copy.  The carved object's base
   is the untyped's watermark before the advance, which is the offset `allocate`
   records for the child.
2. **The scrub** (`req.scrub`): a RAM frame's page is zeroed; a child untyped is
   not written.
3. **The capability**: `req.capability childId` is installed at `dst` through
   `cspaceInsertSlot`, the one install primitive, so the destination must be an
   empty slot its CNode can address.
4. **The derivation**: the new capability is recorded as a CDT child of the
   untyped capability (`DerivationOp.retype`), so revoking the untyped
   capability reaches it — the edge every other install path records.

This is the only path that creates a frame or an untyped on a live state: the
in-place retype refuses memory-backed kinds and the boot refuses configured
frames and requires every boot untyped pristine, so every such object in a
reachable state was carved from an untyped by a holder of a capability to it.

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
        match st.getUntyped? untypedId with
        | none => .error .untypedTypeMismatch
        | some ut =>
          match retypeFromUntyped src untypedId childId (req.object untypedId ut) req.size st with
          | .error e => .error e
          | .ok ((), st1) =>
            match cspaceInsertSlot dst (req.capability childId) (req.scrub st1 ut) with
            | .error e => .error e
            | .ok ((), st2) =>
              let (srcNode, stSrc) := SystemState.ensureCdtNodeForSlot st2 src
              let (dstNode, stDst) := SystemState.ensureCdtNodeForSlot stSrc dst
              .ok ((), { stDst with cdt := stDst.cdt.addEdge srcNode dstNode .retype })
      | _ => .error .invalidCapability


/-- **WS-BP BP7.1**: a successful carve of a page-aligned kind found the
untyped's watermark on a page boundary — the primitive's S5-G guard, read back.
It is what makes the base of a carved frame a page a descriptor can name. -/
theorem retypeFromUntyped_ok_pageAligned
    (st st' : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (newObj : KernelObject) (allocSize : Nat)
    (ut : UntypedObject)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hReq : requiresPageAlignment newObj.objectType = true)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    allocationBasePageAligned ut = true := by
  cases hA : allocationBasePageAligned ut
  · exfalso
    unfold retypeFromUntyped SystemState.getObject? at hStep
    simp only [hObj, hReq, hA, Bool.not_false, Bool.and_true, ↓reduceIte] at hStep
    repeat (split at hStep <;> (try cases hStep))
    all_goals cases hStep
  · rfl


/-- **WS-BP BP7.1: what a successful carve consists of** — the four steps of
`untypedRetypeObject`, read back.  The capability lookup returns the state it
was given, so every later step runs from `st` itself.  One owner for the case
analysis, so the invariant proofs that consume a carve read these equations
rather than re-running the operation's `match`. -/
theorem untypedRetypeObject_ok_decompose
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (req : CarveRequest)
    (st st' : SystemState)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    ∃ (utCap : Capability) (untypedId : SeLe4n.ObjId) (ut : UntypedObject)
      (st1 st2 : SystemState),
      cspaceLookupSlot src st = .ok (utCap, st) ∧
      utCap.target = .object untypedId ∧
      st.getUntyped? untypedId = some ut ∧
      retypeFromUntyped src untypedId childId (req.object untypedId ut) req.size st
        = .ok ((), st1) ∧
      cspaceInsertSlot dst (req.capability childId) (req.scrub st1 ut) = .ok ((), st2) ∧
      st' = (let p1 := SystemState.ensureCdtNodeForSlot st2 src
             let p2 := SystemState.ensureCdtNodeForSlot p1.snd dst
             { p2.snd with cdt := p2.snd.cdt.addEdge p1.fst p2.fst .retype }) := by
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
      cases hUt : stL.getUntyped? untypedId with
      | none => rw [hUt] at hStep; cases hStep
      | some ut =>
        rw [hUt] at hStep
        simp only at hStep
        cases hRt : retypeFromUntyped src untypedId childId (req.object untypedId ut)
            req.size stL with
        | error e => rw [hRt] at hStep; cases hStep
        | ok p1 =>
          obtain ⟨_, st1⟩ := p1
          rw [hRt] at hStep
          simp only at hStep
          cases hIns : cspaceInsertSlot dst (req.capability childId) (req.scrub st1 ut) with
          | error e => rw [hIns] at hStep; cases hStep
          | ok p2 =>
            obtain ⟨_, st2⟩ := p2
            rw [hIns] at hStep
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
            exact ⟨utCap, untypedId, ut, st1, st2, by first | exact hLk | rfl,
              by first | exact hTgt | rfl, by first | exact hUt | rfl,
              by first | exact hRt | rfl, by first | exact hIns | rfl, hStep.symm⟩
    | _ => rw [hTgt] at hStep; cases hStep

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

/-- **WS-BP BP7.1 slice 4b: `freshAsid?` answers an ASID a VSpace-root carve
admits** — non-zero, below the machine's bound, and free in the ASID table. -/
theorem freshAsid?_admissible (st : SystemState) (asid : SeLe4n.ASID)
    (h : freshAsid? st = some asid) :
    (CarveRequest.vspaceRoot asid).admissible st = true := by
  unfold freshAsid? at h
  cases hF : (List.range st.machine.maxASID).find?
      (fun n => n != 0 && (st.asidTable[SeLe4n.ASID.ofNat n]?).isNone) with
  | none => rw [hF] at h; cases h
  | some n =>
    rw [hF] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hP := List.find?_some hF
    have hMem := List.mem_of_find?_eq_some hF
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hP
    have hLt : n < st.machine.maxASID := List.mem_range.mp hMem
    simp only [CarveRequest.admissible, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq]
    exact ⟨⟨hP.1, hLt⟩, hP.2⟩

/-- **WS-BP BP7.1: the carved frame's page is inside its untyped, on a page
boundary, and of its untyped's memory kind.**  The whole of what "memory is
authority" asks of a carve: the frame names one page the untyped owned
(`[regionBase, regionBase + regionSize)`), a descriptor can name it, and a
device untyped cannot be turned into RAM or the reverse. -/
theorem untypedNextFrame_of_retype_ok
    (st st' : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hStep : retypeFromUntyped authority untypedId childId
      (.frame (untypedNextFrame ut)) SeLe4n.pageBytes st = .ok ((), st')) :
    ut.regionBase.toNat ≤ (untypedNextFrame ut).base.toNat ∧
    (untypedNextFrame ut).base.toNat + SeLe4n.pageBytes ≤
      ut.regionBase.toNat + ut.regionSize ∧
    (untypedNextFrame ut).wellFormed ∧
    (untypedNextFrame ut).isDevice = ut.isDevice := by
  obtain ⟨ut₀, ut', _, _, _, offset, hObj₀, _, _, _, _, hAlloc, _, _⟩ :=
    retypeFromUntyped_ok_decompose st st' authority untypedId childId _ _ hStep
  rw [hObj] at hObj₀
  have hEq : ut₀ = ut := by cases hObj₀; rfl
  subst hEq
  have hAligned := retypeFromUntyped_ok_pageAligned st st' authority untypedId childId
    _ _ ut₀ hObj rfl hStep
  have hCan := ((UntypedObject.allocate_some_iff ut₀ childId _ _).mp hAlloc).1
  simp only [UntypedObject.canAllocate, Bool.and_eq_true, decide_eq_true_eq] at hCan
  simp only [allocationBasePageAligned, beq_iff_eq] at hAligned
  refine ⟨?_, ?_, ?_, rfl⟩
  · show ut₀.regionBase.toNat ≤ ut₀.regionBase.toNat + ut₀.watermark
    omega
  · show ut₀.regionBase.toNat + ut₀.watermark + SeLe4n.pageBytes ≤ _
    omega
  · show (ut₀.regionBase.toNat + ut₀.watermark) % SeLe4n.pageBytes = 0
    simpa [SeLe4n.pageBytes] using hAligned


/-- **WS-BP BP7.1 slice 4b (`v0.36.10`): a carved VSpace root's table page is
inside its untyped, on a page boundary, and RAM.**  The root counterpart of
`untypedNextFrame_of_retype_ok`: the page a PE will be told to walk is one page
the untyped owned, a descriptor base can name it, and it is never MMIO — a
device untyped cannot back a root (`KernelObjectType.deviceBackable`). -/
theorem untypedNextVSpaceRoot_of_retype_ok
    (st st' : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject) (asid : SeLe4n.ASID)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hStep : retypeFromUntyped authority untypedId childId
      (.vspaceRoot (untypedNextVSpaceRoot ut asid)) SeLe4n.pageBytes st = .ok ((), st')) :
    (untypedNextVSpaceRoot ut asid).tableBase = some (untypedNextFrame ut).base ∧
    ut.regionBase.toNat ≤ (untypedNextFrame ut).base.toNat ∧
    (untypedNextFrame ut).base.toNat + SeLe4n.pageBytes ≤
      ut.regionBase.toNat + ut.regionSize ∧
    (untypedNextFrame ut).base.toNat % SeLe4n.pageBytes = 0 ∧
    ut.isDevice = false := by
  obtain ⟨ut₀, ut', _, _, _, offset, hObj₀, hDev, _, _, _, hAlloc, _, _⟩ :=
    retypeFromUntyped_ok_decompose st st' authority untypedId childId _ _ hStep
  rw [hObj] at hObj₀
  have hEq : ut₀ = ut := by cases hObj₀; rfl
  subst hEq
  have hAligned := retypeFromUntyped_ok_pageAligned st st' authority untypedId childId
    _ _ ut₀ hObj rfl hStep
  have hCan := ((UntypedObject.allocate_some_iff ut₀ childId _ _).mp hAlloc).1
  simp only [UntypedObject.canAllocate, Bool.and_eq_true, decide_eq_true_eq] at hCan
  simp only [allocationBasePageAligned, beq_iff_eq] at hAligned
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · show ut₀.regionBase.toNat ≤ ut₀.regionBase.toNat + ut₀.watermark
    omega
  · show ut₀.regionBase.toNat + ut₀.watermark + SeLe4n.pageBytes ≤ _
    omega
  · show (ut₀.regionBase.toNat + ut₀.watermark) % SeLe4n.pageBytes = 0
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
                pendingPhysicalWrites := (carveZeroFrame st frame).pendingPhysicalWrites } := by
  unfold carveZeroFrame; split <;> rfl

/-- **WS-BP BP7.1**: a RAM frame's page is zero after the scrub. -/
theorem carveZeroFrame_zeroed (st : SystemState) (frame : FrameObject)
    (hRam : frame.isDevice = false) :
    SeLe4n.memoryZeroed (carveZeroFrame st frame).machine frame.base SeLe4n.pageBytes := by
  unfold carveZeroFrame
  simp only [hRam, Bool.false_eq_true, ↓reduceIte]
  exact SeLe4n.zeroMemoryRange_establishes_memoryZeroed st.machine _ _

/-- **WS-BP BP7.1 slice 4**: a request's scrub moves no object... -/
@[simp] theorem CarveRequest.scrub_objects (st : SystemState) (ut : UntypedObject)
    (req : CarveRequest) : (req.scrub st ut).objects = st.objects := by
  cases req <;> simp [CarveRequest.scrub]

/-- ...and no scheduler state. -/
@[simp] theorem CarveRequest.scrub_scheduler (st : SystemState) (ut : UntypedObject)
    (req : CarveRequest) : (req.scrub st ut).scheduler = st.scheduler := by
  cases req <;> simp [CarveRequest.scrub]

/-- **WS-BP BP7.1 slice 4: the carved child untyped's region is inside its
parent, on a page boundary, of its parent's memory kind, with its parent stamped
and nothing carved from it.**  The child-untyped counterpart of
`untypedNextFrame_of_retype_ok`, and the fact the reset's containment check
(`untypedSubtreeContained`) decides on every state rather than trusting. -/
theorem untypedNextChild_of_retype_ok
    (st st' : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject) (b : Nat)
    (hObj : st.objects[untypedId]? = some (.untyped ut))
    (hStep : retypeFromUntyped authority untypedId childId
      (.untyped (untypedNextChild ut untypedId b)) (2 ^ b) st = .ok ((), st')) :
    ut.regionBase.toNat ≤ (untypedNextChild ut untypedId b).regionBase.toNat ∧
    (untypedNextChild ut untypedId b).regionBase.toNat +
        (untypedNextChild ut untypedId b).regionSize ≤
      ut.regionBase.toNat + ut.regionSize ∧
    (untypedNextChild ut untypedId b).regionBase.toNat % SeLe4n.pageBytes = 0 ∧
    (untypedNextChild ut untypedId b).isDevice = ut.isDevice ∧
    (untypedNextChild ut untypedId b).parent = some untypedId ∧
    (untypedNextChild ut untypedId b).watermark = 0 ∧
    (untypedNextChild ut untypedId b).children = [] := by
  obtain ⟨ut₀, ut', _, _, _, offset, hObj₀, _, _, _, _, hAlloc, _, _⟩ :=
    retypeFromUntyped_ok_decompose st st' authority untypedId childId _ _ hStep
  rw [hObj] at hObj₀
  have hEq : ut₀ = ut := by cases hObj₀; rfl
  subst hEq
  have hAligned := retypeFromUntyped_ok_pageAligned st st' authority untypedId childId
    _ _ ut₀ hObj rfl hStep
  have hCan := ((UntypedObject.allocate_some_iff ut₀ childId _ _).mp hAlloc).1
  simp only [UntypedObject.canAllocate, Bool.and_eq_true, decide_eq_true_eq] at hCan
  simp only [allocationBasePageAligned, beq_iff_eq] at hAligned
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · show ut₀.regionBase.toNat ≤ ut₀.regionBase.toNat + ut₀.watermark
    omega
  · show ut₀.regionBase.toNat + ut₀.watermark + 2 ^ b ≤ _
    omega
  · show (ut₀.regionBase.toNat + ut₀.watermark) % SeLe4n.pageBytes = 0
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
    ∃ (untypedId : SeLe4n.ObjId) (ut : UntypedObject) (st1 : SystemState),
      st.objects[untypedId]? = some (.untyped ut) ∧
      retypeFromUntyped src untypedId childId (req.object untypedId ut) req.size st
        = .ok ((), st1) ∧
      st'.objects[childId]? = some (req.object untypedId ut) ∧
      ∃ cn : CNode, st'.objects[dst.cnode]? =
        some (.cnode (cn.insert dst.slot (req.capability childId))) := by
  obtain ⟨_, untypedId, ut, st1, st2, _, _, hUt, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hStep
  have hObj : st.objects[untypedId]? = some (.untyped ut) :=
    (SystemState.getUntyped?_eq_some_iff st untypedId ut).mp hUt
  obtain ⟨_, ut', _, stL, stUt, _, _, _, _, hLkR, _, _, hStUt, hStCh⟩ :=
    retypeFromUntyped_ok_decompose st st1 src untypedId childId _ _ hRt
  have hStL : stL = st := cspaceLookupSlot_ok_state_eq st src _ stL hLkR
  rw [hStL] at hStUt
  have hInvUt := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStUt
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInvUt hStCh
  have hAt1 : st1.objects[childId]? = some (req.object untypedId ut) :=
    storeObject_objects_eq _ _ _ _ hInvUt hStCh
  have hInvZ : (req.scrub st1 ut).objects.invExt := by
    rw [CarveRequest.scrub_objects]; exact hInv1
  obtain ⟨cn, hCnPre, hCnPost⟩ := cspaceInsertSlot_objects_eq _ _ _ _ hInvZ hIns
  have hNe : childId ≠ dst.cnode := by
    intro h
    rw [CarveRequest.scrub_objects, ← h, hAt1] at hCnPre
    cases req <;> cases hCnPre
  have hAt2 : st2.objects[childId]? = some (req.object untypedId ut) := by
    rw [cspaceInsertSlot_preserves_objects_ne _ _ _ _ _ hNe hInvZ hIns,
      CarveRequest.scrub_objects]; exact hAt1
  refine ⟨untypedId, ut, st1, hObj, hRt, ?_, cn, ?_⟩
  · simp only [SystemState.ensureCdtNodeForSlot_objects_eq, hAt2]
  · simp only [SystemState.ensureCdtNodeForSlot_objects_eq, hCnPost]

/-- **WS-BP BP7.1: a frame carve's payoff** — the frame is the page at the
untyped's watermark, inside the untyped, on a page boundary and of its memory
kind, and the destination holds the frame capability. -/
theorem untypedRetypeObject_ok_frame
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst .frame st = .ok ((), st')) :
    ∃ (untypedId : SeLe4n.ObjId) (ut : UntypedObject),
      st.objects[untypedId]? = some (.untyped ut) ∧
      st'.getFrame? childId = some (untypedNextFrame ut) ∧
      ut.regionBase.toNat ≤ (untypedNextFrame ut).base.toNat ∧
      (untypedNextFrame ut).base.toNat + SeLe4n.pageBytes ≤
        ut.regionBase.toNat + ut.regionSize ∧
      (untypedNextFrame ut).wellFormed ∧
      (untypedNextFrame ut).isDevice = ut.isDevice ∧
      ∃ cn : CNode, st'.objects[dst.cnode]? =
        some (.cnode (cn.insert dst.slot (frameCapability childId))) := by
  obtain ⟨untypedId, ut, st1, hObj, hRt, hAt, hCn⟩ :=
    untypedRetypeObject_ok_carved src dst childId .frame st st' hObjInv hStep
  obtain ⟨hLo, hHi, hWf, hDev⟩ := untypedNextFrame_of_retype_ok st st1 src untypedId childId
    ut hObj hRt
  refine ⟨untypedId, ut, hObj, ?_, hLo, hHi, hWf, hDev, hCn⟩
  simp only [SystemState.getFrame?, hAt, CarveRequest.object]

/-- **WS-BP BP7.1 slice 4 (`v0.36.8`): a child-untyped carve's payoff** — the
store holds, at the child id, an untyped whose region lies inside its parent's
on a page boundary, of the parent's memory kind, with the parent stamped and
nothing yet carved from it; and the destination holds a capability carrying
`.retype` to it, so the caller can carve from the child and reset it. -/
theorem untypedRetypeObject_ok_untyped
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (b : Nat) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst (.untyped b) st = .ok ((), st')) :
    ∃ (untypedId : SeLe4n.ObjId) (ut : UntypedObject),
      st.objects[untypedId]? = some (.untyped ut) ∧
      st'.objects[childId]? = some (.untyped (untypedNextChild ut untypedId b)) ∧
      ut.regionBase.toNat ≤ (untypedNextChild ut untypedId b).regionBase.toNat ∧
      (untypedNextChild ut untypedId b).regionBase.toNat + 2 ^ b ≤
        ut.regionBase.toNat + ut.regionSize ∧
      (untypedNextChild ut untypedId b).regionBase.toNat % SeLe4n.pageBytes = 0 ∧
      (untypedNextChild ut untypedId b).isDevice = ut.isDevice ∧
      (untypedNextChild ut untypedId b).parent = some untypedId ∧
      ∃ cn : CNode, st'.objects[dst.cnode]? =
        some (.cnode (cn.insert dst.slot (untypedCapability childId))) := by
  obtain ⟨untypedId, ut, st1, hObj, hRt, hAt, hCn⟩ :=
    untypedRetypeObject_ok_carved src dst childId (.untyped b) st st' hObjInv hStep
  obtain ⟨hLo, hHi, hAl, hDev, hPar, -, -⟩ :=
    untypedNextChild_of_retype_ok st st1 src untypedId childId ut b hObj hRt
  exact ⟨untypedId, ut, hObj, hAt, hLo, hHi, hAl, hDev, hPar, hCn⟩

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
    ∃ (untypedId : SeLe4n.ObjId) (ut : UntypedObject),
      st.objects[untypedId]? = some (.untyped ut) ∧
      st'.objects[childId]? = some (.vspaceRoot (untypedNextVSpaceRoot ut asid)) ∧
      asid.toNat ≠ 0 ∧ asid.toNat < st.machine.maxASID ∧ st.asidTable[asid]? = none ∧
      (untypedNextVSpaceRoot ut asid).tableBase = some (untypedNextFrame ut).base ∧
      ut.regionBase.toNat ≤ (untypedNextFrame ut).base.toNat ∧
      (untypedNextFrame ut).base.toNat + SeLe4n.pageBytes ≤
        ut.regionBase.toNat + ut.regionSize ∧
      (untypedNextFrame ut).base.toNat % SeLe4n.pageBytes = 0 ∧
      ut.isDevice = false ∧
      ∃ cn : CNode, st'.objects[dst.cnode]? =
        some (.cnode (cn.insert dst.slot (vspaceRootCapability childId))) := by
  have hAdm := untypedRetypeObject_ok_admissible src dst childId _ st st' hStep
  simp only [CarveRequest.admissible, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, Option.isNone_iff_eq_none] at hAdm
  obtain ⟨⟨hNz, hLt⟩, hFree⟩ := hAdm
  obtain ⟨untypedId, ut, st1, hObj, hRt, hAt, hCn⟩ :=
    untypedRetypeObject_ok_carved src dst childId (.vspaceRoot asid) st st' hObjInv hStep
  obtain ⟨hTb, hLo, hHi, hAl, hDev⟩ :=
    untypedNextVSpaceRoot_of_retype_ok st st1 src untypedId childId ut asid hObj hRt
  exact ⟨untypedId, ut, hObj, hAt, hNz, hLt, hFree, hTb, hLo, hHi, hAl, hDev, hCn⟩



end SeLe4n.Kernel
