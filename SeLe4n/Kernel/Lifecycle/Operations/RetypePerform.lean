-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.ScrubAndUntyped

/-!
# The carve split into its checks and its writes

WS-ZA ZA5.4: `untypedRetypeObject` as seL4 splits `Untyped_Retype` into
`decodeUntypedInvocation` and `invokeUntyped`.  `untypedRetypeAdmittedAt` is
every refusal the carve makes, read from the state it is handed before anything
is written; `untypedRetypePerformAt` is the carve's writes, total.  An admitted
carve is its writes (`untypedRetypeObject_of_admitted`), so the dispatcher hands
the state to the writes alone and every table they write is written in place.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-ZA ZA5.4: **the untyped once `size` bytes are carved from it for
`childId` at free index `idx`** — `UntypedObject.allocate`'s record, total. -/
@[inline] def _root_.SeLe4n.Model.UntypedObject.allocated (ut : UntypedObject) (idx : Nat)
    (childId : SeLe4n.ObjId) (size : Nat) : UntypedObject :=
  { ut with
      children := { objId := childId, offset := idx, size := size } :: ut.children }

theorem _root_.SeLe4n.Model.UntypedObject.allocate_eq_allocated (ut : UntypedObject) (idx : Nat)
    (childId : SeLe4n.ObjId) (size : Nat) (h : ut.canAllocate idx size = true) :
    ut.allocate idx childId size = some (ut.allocated idx childId size, idx) := by
  unfold UntypedObject.allocate UntypedObject.allocated
  rw [if_pos h]

/-- WS-ZA ZA5.4: the state a store leaves — `storeObject` never refuses. -/
@[inline] def storedState (id : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState) :
    SystemState :=
  match storeObject id obj st with
  | .ok ((), st') => st'
  | .error _ => st

theorem storeObject_eq_storedState (id : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState) :
    storeObject id obj st = .ok ((), storedState id obj st) := rfl

/-- WS-ZA ZA5.4: `storedState` as compiled: `storeObjectImpl`'s branches read as
states, so the store's result is never built. -/
@[inline] def storedStateImpl (id : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState) :
    SystemState :=
  if storeLeavesIndexAndTypes st id obj.objectType then withObjectInserted st id obj
  else if storeIsFresh st id then storeFresh st id obj
  else match storeObjectImpl id obj st with
    | .ok ((), st') => st'
    | .error _ => st

@[csimp] theorem storedState_eq_impl : @storedState = @storedStateImpl := by
  funext id obj st
  unfold storedState storedStateImpl
  rw [storeObject_eq_impl]
  unfold storeObjectImpl
  by_cases h1 : storeLeavesIndexAndTypes st id obj.objectType = true
  · simp only [h1, ↓reduceIte, withObjectInserted]
  · by_cases h2 : storeIsFresh st id = true
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

/-- WS-ZA ZA5.4: whether no child of the list is recorded at `childId`, read
entry by entry, so no predicate closure is built. -/
def childrenNameNone (childId : SeLe4n.ObjId) : List UntypedChild → Bool
  | [] => true
  | c :: cs => if c.objId == childId then false else childrenNameNone childId cs

theorem childrenNameNone_eq (childId : SeLe4n.ObjId) (cs : List UntypedChild) :
    childrenNameNone childId cs = !cs.any (fun c => c.objId == childId) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    unfold childrenNameNone
    by_cases h : (c.objId == childId) = true
    · simp [h]
    · simp [h, ih]

/-- WS-ZA ZA5.4: **`retypeFromUntyped`'s refusals** for an untyped `ut` at
`untypedId`, the authority capability `authCap` already read from the slot
`authCnode`/`authSlot`, read before any write; the carve is at the index it
starts from (`retypeFreeIndex`: `authCap`'s free index, or 0 through a slot with
no derivation child) rounded up to the carve's boundary (`alignedCarveIndex`).
The new object enters as its type `ty` alone, so the check builds no object, and
the slot as its two words, so no slot reference is built. -/
def retypeFromUntypedAdmitted (st : SystemState) (authCnode : SeLe4n.ObjId)
    (authSlot : SeLe4n.Slot) (authCap : Capability)
    (untypedId childId : SeLe4n.ObjId) (ty : KernelObjectType) (size : Nat)
    (ut : UntypedObject) : Bool :=
  !decide (st.objects.size ≥ maxObjects) &&
  !decide (childId = untypedId) &&
  !((st.getObject? childId).isSome || isIrqNodeObjId InterruptLineSet.capacity childId) &&
  childrenNameNone childId ut.children &&
  !(ut.isDevice && !ty.deviceBackable) &&
  objectIdInAddressSpace st.machine childId &&
  !decide (size < objectTypeAllocSize ty) &&
  lifecycleRetypeAuthority authCap untypedId &&
  retypeResetAdmitted st { cnode := authCnode, slot := authSlot } ut &&
  ut.canAllocate (alignedCarveIndex ty size ut
    (retypeFreeIndex st { cnode := authCnode, slot := authSlot } authCap)) size

/-- WS-ZA ZA5.4: **`retypeFromUntyped`'s writes**: the child recorded in the
untyped at free index `idx`, the new object stored at its id, and the authority
capability's free index advanced past it in its slot. -/
@[inline] def retypeFromUntypedWrites (authority : CSpaceAddr) (idx : Nat)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject) (size : Nat) (ut : UntypedObject) (st : SystemState) :
    SystemState :=
  setCapFreeIndex
    (storedState childId newObj (storedState untypedId (.untyped (ut.allocated idx childId size)) st))
    authority (idx + size)

/-- WS-ZA ZA5.4: **an admitted `retypeFromUntyped` is its writes.** -/
theorem retypeFromUntyped_of_admitted {st : SystemState} {authority : CSpaceAddr}
    {authCap : Capability} {untypedId childId : SeLe4n.ObjId} {newObj : KernelObject}
    {size : Nat} {ut : UntypedObject}
    (hLk : SystemState.lookupSlotCap st authority = some authCap)
    (hUt : st.getObject? untypedId = some (.untyped ut))
    (hA : retypeFromUntypedAdmitted st authority.cnode authority.slot authCap untypedId childId
      newObj.objectType size ut = true) :
    retypeFromUntyped authority untypedId childId newObj size st =
      .ok ((), retypeFromUntypedWrites authority
        (alignedCarveIndex newObj.objectType size ut (retypeFreeIndex st authority authCap))
        untypedId childId newObj size ut st) := by
  unfold retypeFromUntypedAdmitted at hA
  rw [childrenNameNone_eq] at hA
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hA
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hCap, hSelf⟩, hFresh⟩, hKids⟩, hDev⟩, hAddr⟩, hSize⟩, hAuth⟩, hReset⟩, hCan⟩ := hA
  have hLkS : cspaceLookupSlot authority st = .ok (authCap, st) := by
    unfold cspaceLookupSlot; rw [hLk]
  unfold retypeFromUntyped
  simp only [hUt, hCap, hSelf, hFresh, hKids, hDev, hAddr, hSize, hLkS, hAuth, hReset,
    UntypedObject.allocate_eq_allocated ut _ childId size hCan, ↓reduceIte,
    Bool.false_eq_true, storeObject_eq_storedState]
  rfl

/-- WS-ZA ZA5.4: **every refusal of `untypedRetypeObject`**, read from the state
it is handed: the kernel heap's capacity for what the carve makes
(`CarveRequest.heapAdmitted`, first, as the carve asks it first), the request's
own precondition, the untyped capability in `src` naming an untyped, the
destination slot, and the carve's checks. -/
@[inline] def untypedRetypeAdmittedAt (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (req : CarveRequest) : Bool :=
  req.heapAdmitted st && req.admissible st &&
  match SystemState.lookupSlotCap st src with
  | some utCap =>
    match utCap.target with
    | .object untypedId =>
      match st.getUntyped? untypedId with
      | some ut =>
        cspaceDstAdmitted dst st &&
        retypeFromUntypedAdmitted st src.cnode src.slot utCap untypedId childId req.objectType
          req.size ut
      | none => false
    | _ => false
  | none => false

/-- WS-ZA ZA5.4: **`untypedRetypeObject`'s writes**: the carve, the scrub, the
capability written into the destination slot, and its derivation edge. -/
def untypedRetypePerformAt (src dst : CSpaceAddr) (childId : SeLe4n.ObjId)
    (req : CarveRequest) (st : SystemState) : SystemState :=
  match SystemState.lookupSlotCap st src with
  | some utCap =>
    match utCap.target with
    | .object untypedId =>
      match st.getUntyped? untypedId with
      | some ut =>
        let idx := req.carveIndex ut (retypeFreeIndex st src utCap)
        let st1 := retypeFromUntypedWrites src idx untypedId childId
          (req.object untypedId childId ut idx) req.size ut st
        ((req.scrub st1 ut idx).storeCNodeWith dst.cnode
          (·.insert dst.slot (req.capability childId))).cdtAddChild src dst .retype
      | none => st
    | _ => st
  | none => st

/-- WS-ZA ZA5.4: **an admitted carve is its writes.** -/
theorem untypedRetypeObject_of_admitted {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st : SystemState}
    (hA : untypedRetypeAdmittedAt st src dst childId req = true) :
    untypedRetypeObject src childId dst req st =
      .ok ((), untypedRetypePerformAt src dst childId req st) := by
  unfold untypedRetypeAdmittedAt at hA
  simp only [Bool.and_eq_true] at hA
  obtain ⟨⟨hHeap, hAdm⟩, hRest⟩ := hA
  unfold untypedRetypeObject untypedRetypePerformAt
  simp only [hHeap, hAdm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hL : SystemState.lookupSlotCap st src with
  | none => rw [hL] at hRest; cases hRest
  | some utCap =>
    rw [hL] at hRest
    dsimp only at hRest
    have hLkS : cspaceLookupSlot src st = .ok (utCap, st) := by
      unfold cspaceLookupSlot; rw [hL]
    rw [hLkS]
    dsimp only
    cases hT : utCap.target with
    | object untypedId =>
      rw [hT] at hRest
      dsimp only at hRest ⊢
      cases hU : st.getUntyped? untypedId with
      | none => rw [hU] at hRest; cases hRest
      | some ut =>
        rw [hU] at hRest
        simp only [Bool.and_eq_true] at hRest
        obtain ⟨hD, hR⟩ := hRest
        have hUt : st.getObject? untypedId = some (.untyped ut) :=
          (SystemState.getUntyped?_eq_some_iff st untypedId ut).mp hU
        have hAu : lifecycleRetypeAuthority utCap untypedId = true := by
          revert hR; unfold retypeFromUntypedAdmitted; simp only [Bool.and_eq_true]
          intro h; exact h.1.1.2
        simp only [hAu, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [(cspaceDstRefusal_eq_ok_iff dst st).mpr hD]
        dsimp only
        rw [← CarveRequest.object_objectType untypedId childId ut
          (req.carveIndex ut (retypeFreeIndex st src utCap))] at hR
        rw [retypeFromUntyped_of_admitted hL hUt hR, CarveRequest.object_objectType]
        rfl
    | _ => rw [hT] at hRest; cases hRest

/-- `cspaceDstRefusal`, inlined, so its caller reads the destination's two
words and builds no slot reference. -/
@[inline] def untypedRetypeDstRefusal (dst : CSpaceAddr) (st : SystemState) :
    Except KernelError Unit :=
  match st.getCNode? dst.cnode with
  | some cn =>
      if !cn.slotAddressable dst.slot then .error (.invalidArgument 0)
      else
        match cn.lookup dst.slot with
        | some _ => .error .targetSlotOccupied
        | none => .ok ()
  | none => .error .objectNotFound

theorem untypedRetypeDstRefusal_eq (dst : CSpaceAddr) (st : SystemState) :
    untypedRetypeDstRefusal dst st = cspaceDstRefusal dst st := rfl

/-- **The refusal `untypedRetypeObject` answers**, read from the checks'
results in the specification's order, without building the request or
running the carve: the heap's (`heapOk`), the request's (`admissibleOk`), the
issuing slot's, the destination's, then `retypeFromUntyped`'s.  Every result
is a word or a shared constant.  An admitted carve has no refusal, and reads
`illegalState` here (`untypedRetypeObject_refused` holds only for a refused
one). -/
@[inline] def untypedRetypeRefusalWith (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (heapOk admissibleOk : Bool) (ty : KernelObjectType)
    (size : Nat) : KernelError :=
  if !heapOk then .untypedRegionExhausted st.machine.kernelHeapFreeBytes.toUInt64 else
  if !admissibleOk then .illegalState else
  match SystemState.lookupSlotCap st src with
  | none =>
    match st.getCNode? src.cnode with
    | some _ => .invalidCapability 0
    | none => .objectNotFound
  | some utCap =>
    match utCap.target with
    | .object untypedId =>
      if !lifecycleRetypeAuthority utCap untypedId then .illegalAuthority else
      match st.getUntyped? untypedId with
      | none => .untypedTypeMismatch
      | some ut =>
        match untypedRetypeDstRefusal dst st with
        | .error e => e
        | .ok () =>
          if st.objects.size ≥ maxObjects then .objectStoreCapacityExceeded
          else if childId = untypedId then .childIdSelfOverwrite
          else if (st.getObject? childId).isSome ||
              isIrqNodeObjId InterruptLineSet.capacity childId then .childIdCollision
          else if !childrenNameNone childId ut.children then .childIdCollision
          else if ut.isDevice && !ty.deviceBackable then .untypedDeviceRestriction
          else if !objectIdInAddressSpace st.machine childId then .addressOutOfBounds
          else if size < objectTypeAllocSize ty then .untypedAllocSizeTooSmall
          else if !retypeResetAdmitted st src ut then .revocationRequired
          else if !ut.canAllocate (alignedCarveIndex ty size ut (retypeFreeIndex st src utCap)) size then
            .untypedRegionExhausted (ut.regionSize - retypeFreeIndex st src utCap).toUInt64
          else .illegalState
    | _ => .invalidCapability 0

/-- **A refused carve answers `untypedRetypeRefusalWith`**, and writes
nothing: the compiled dispatch answers it without decoding the invocation
again. -/
theorem untypedRetypeObject_refused {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st : SystemState}
    (hA : untypedRetypeAdmittedAt st src dst childId req = false) :
    untypedRetypeObject src childId dst req st =
      .error (untypedRetypeRefusalWith st src dst childId (req.heapAdmitted st)
        (req.admissible st) req.objectType req.size) := by
  unfold untypedRetypeAdmittedAt at hA
  unfold untypedRetypeObject untypedRetypeRefusalWith
  rw [untypedRetypeDstRefusal_eq]
  simp only [childrenNameNone_eq, Bool.not_not]
  cases hH : req.heapAdmitted st
  · rfl
  cases hM : req.admissible st
  · simp
  simp only [hH, hM, Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hA ⊢
  cases hL : SystemState.lookupSlotCap st src with
  | none =>
    cases hC : st.getCNode? src.cnode <;> simp [cspaceLookupSlot, hL, hC]
  | some utCap =>
    rw [hL] at hA
    dsimp only at hA
    have hLkS : cspaceLookupSlot src st = .ok (utCap, st) := by
      unfold cspaceLookupSlot; rw [hL]
    rw [hLkS]
    dsimp only
    cases hT : utCap.target with
    | object untypedId =>
      rw [hT] at hA
      dsimp only at hA ⊢
      cases hAu : lifecycleRetypeAuthority utCap untypedId
      · simp
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hU : st.getUntyped? untypedId with
      | none => rfl
      | some ut =>
        rw [hU] at hA
        dsimp only at hA ⊢
        have hUt : st.getObject? untypedId = some (.untyped ut) :=
          (SystemState.getUntyped?_eq_some_iff st untypedId ut).mp hU
        cases hD : cspaceDstRefusal dst st with
        | error e => rfl
        | ok u =>
          have hDA := (cspaceDstRefusal_eq_ok_iff dst st).mp hD
          rw [hDA, Bool.true_and] at hA
          dsimp only
          unfold retypeFromUntyped
          rw [hUt, CarveRequest.object_objectType]
          dsimp only
          unfold retypeFromUntypedAdmitted at hA
          rw [childrenNameNone_eq] at hA
          have hLkS' : cspaceLookupSlot src st = .ok (utCap, st) := hLkS
          by_cases h1 : st.objects.size ≥ maxObjects
          · simp only [h1, ↓reduceIte]
          by_cases h2 : childId = untypedId
          · simp only [h1, h2, ↓reduceIte]
          by_cases h3 : ((st.getObject? childId).isSome ||
              isIrqNodeObjId InterruptLineSet.capacity childId) = true
          · simp only [h1, h2, h3, ↓reduceIte]
          rw [Bool.not_eq_true] at h3
          by_cases h4 : (ut.children.any (fun c => c.objId == childId)) = true
          · simp only [h1, h2, h3, h4, ↓reduceIte, Bool.false_eq_true]
          rw [Bool.not_eq_true] at h4
          by_cases h5 : (ut.isDevice && !req.objectType.deviceBackable) = true
          · simp only [h1, h2, h3, h4, h5, ↓reduceIte, Bool.false_eq_true]
          rw [Bool.not_eq_true] at h5
          cases h6 : objectIdInAddressSpace st.machine childId
          · simp only [h1, h2, h3, h4, h5, ↓reduceIte, Bool.false_eq_true, Bool.not_false]
          by_cases h7 : req.size < objectTypeAllocSize req.objectType
          · simp only [h1, h2, h3, h4, h5, h7, ↓reduceIte, Bool.false_eq_true, Bool.not_true]
          cases h8 : retypeResetAdmitted st src ut
          · simp only [h1, h2, h3, h4, h5, h7, hLkS', hAu, ↓reduceIte, Bool.false_eq_true,
              Bool.not_true, Bool.not_false]
          cases h9 : ut.canAllocate (alignedCarveIndex req.objectType req.size ut
              (retypeFreeIndex st src utCap)) req.size
          · simp only [h1, h2, h3, h4, h5, h7, h9, hLkS', hAu, UntypedObject.allocate,
              ↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false]
          · exfalso
            simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hAu, decide_false, Bool.not_false,
              Bool.and_true, Bool.true_eq_false] at hA
    | _ => rfl


/-- **A carve the kernel heap cannot hold is not admitted**, so the compiled
dispatch (`RefusalCarrying.ofChecked`) never runs its writes and answers the
carve's own refusal (`untypedRetypeObject_heapRefused`) in the state it was
handed. -/
theorem untypedRetypeAdmittedAt_heapRefused {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st : SystemState} (hHeap : req.heapAdmitted st = false) :
    untypedRetypeAdmittedAt st src dst childId req = false := by
  unfold untypedRetypeAdmittedAt
  simp only [hHeap, Bool.false_and]

/-- The split carve, refused by the heap: its checks fail, so its writes never
run, and the refusal is the carve's own, in the state it was handed. -/
theorem untypedRetypeOfChecked_heapRefused {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st : SystemState} (hHeap : req.heapAdmitted st = false) :
    RefusalCarrying.ofChecked (untypedRetypeAdmittedAt st src dst childId req)
        (untypedRetypePerformAt src dst childId req)
        (untypedRetypeObject src childId dst req) st =
      .error (.untypedRegionExhausted st.machine.kernelHeapFreeBytes.toUInt64, st) := by
  unfold RefusalCarrying.ofChecked
  rw [untypedRetypeAdmittedAt_heapRefused hHeap,
    untypedRetypeObject_heapRefused src dst childId req st hHeap]
  rfl

/-- WS-ZA ZA5.4: `CarveRequest.scrub` with the carved page's base and memory
kind read as words, so the scrub builds no frame record. -/
@[inline] def CarveRequest.scrubAt (st : SystemState) (base : SeLe4n.PAddr) (isDevice : Bool) :
    CarveRequest → SystemState
  | .frame =>
      if isDevice then st
      else { st with
              machine := SeLe4n.zeroMemoryRange st.machine base SeLe4n.pageBytes
              physicalWrites := st.physicalWrites.pushAfter st.physicalWritesDrained
                (SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage base)
              physicalWritesDrained := false }
  | .untyped _ => st
  | .vspaceRoot _ =>
      { st with
          machine := SeLe4n.zeroMemoryRange st.machine base SeLe4n.pageBytes
          physicalWrites := st.physicalWrites.pushAfter st.physicalWritesDrained
            (SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage base)
          physicalWritesDrained := false }
  | .pageTable =>
      { st with
          machine := SeLe4n.zeroMemoryRange st.machine base SeLe4n.pageBytes
          physicalWrites := st.physicalWrites.pushAfter st.physicalWritesDrained
            (SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage base)
          physicalWritesDrained := false }
  | .tcb _ _ | .endpoint | .notification | .cnode _ _ | .reply | .schedContext _ => st

theorem CarveRequest.scrub_eq_scrubAt (st : SystemState) (ut : UntypedObject) (idx : Nat)
    (req : CarveRequest) :
    req.scrub st ut idx = req.scrubAt st (untypedNextFrame ut idx).base ut.isDevice := by
  cases req <;> rfl

/-- WS-ZA ZA5.4: `untypedRetypePerformAt` as compiled.  Everything the carve
reads of the untyped and of the invoked capability — the free index, the new
object, the page's base and kind — is read before either is written, so the
untyped records its child in its slot (`storeUntypedWith`) and the capability
takes its advanced index in its own cell (`CNode.setFreeIndexCells`); the scrub
reads words (`CarveRequest.scrubAt`), and the new capability goes into its
slot's own record (`CNode.insertObjectCap`). -/
def untypedRetypePerformWords (srcCnode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (dstCnode : SeLe4n.ObjId) (dstSlot : SeLe4n.Slot) (childId : SeLe4n.ObjId)
    (req : CarveRequest) (st : SystemState) : SystemState :=
  match SystemState.lookupSlotCap st ⟨srcCnode, srcSlot⟩ with
  | some utCap =>
    match utCap.target with
    | .object untypedId =>
      match st.getUntyped? untypedId with
      | some ut =>
        let idx := req.carveIndex ut (retypeFreeIndex st ⟨srcCnode, srcSlot⟩ utCap)
        let newObj := req.object untypedId childId ut idx
        let base := (untypedNextFrame ut idx).base
        let isDevice := ut.isDevice
        let size := req.size
        let st1 := st.storeUntypedWith untypedId (·.allocated idx childId size)
        let st2 := storedState childId newObj st1
        let st3 := st2.storeCNodeWith srcCnode (·.setFreeIndexCells srcSlot (idx + size))
        ((req.scrubAt st3 base isDevice).storeCNodeWith dstCnode
          (·.insertObjectCap dstSlot childId req.rights)).cdtAddChild
            ⟨srcCnode, srcSlot⟩ ⟨dstCnode, dstSlot⟩ .retype
      | none => st
    | _ => st
  | none => st

/-- `untypedRetypePerformAt` is its words form, with the slots handed on as
words. -/
theorem untypedRetypePerformAt_eq_words (src dst : CSpaceAddr) (childId : SeLe4n.ObjId)
    (req : CarveRequest) (st : SystemState) :
    untypedRetypePerformAt src dst childId req st =
      untypedRetypePerformWords src.cnode src.slot dst.cnode dst.slot childId req st := by
  obtain ⟨sc, ss⟩ := src
  obtain ⟨dc, ds⟩ := dst
  unfold untypedRetypePerformAt untypedRetypePerformWords
  dsimp only
  split
  · next utCap _ =>
    split
    · next untypedId _ =>
      cases hU : st.getUntyped? untypedId with
      | none => rfl
      | some ut =>
        have hObj : st.objects[untypedId]? = some (.untyped ut) :=
          (SystemState.getUntyped?_eq_some_iff st untypedId ut).mp hU
        dsimp only
        unfold retypeFromUntypedWrites
        rw [CarveRequest.scrub_eq_scrubAt]
        have hS := SystemState.storeObject_untyped_eq_storeUntypedWith hObj
          (·.allocated (req.carveIndex ut (retypeFreeIndex st ⟨sc, ss⟩ utCap)) childId req.size)
        rw [setCapFreeIndex_eq_impl]
        unfold setCapFreeIndexImpl
        have hF : ∀ cn : CNode, cn.insertObjectCap ds childId req.rights =
            cn.insert ds (req.capability childId) := by
          intro cn; rw [CNode.insertObjectCap_eq_insert, CarveRequest.capability_eq]
        simp only [storedState, hS, hF]
    · rfl
  · rfl

/-! ## The carve read from its request's words

WS-ZA ZA6.35: a decoded request is words, as seL4's `decodeUntypedInvocation`
hands `invokeUntyped` the object type and size it read from the message
registers: the kind's code, the size, and the thread's domain and core or the
root's ASID.  The compiled dispatch carries the words and reads each function of
the request off them, so it builds no request (`untypedRetypePerformCode_eq`,
`untypedRetypeAdmittedCode_eq`). -/

/-- The request the words name: kind `k` (0 frame, 1 untyped, 2 VSpace root,
3 page table, 4 thread, 5 endpoint, 6 notification, 7 CNode, 8 reply, 9 and
above scheduling context), size or radix `n`, a thread's `dom` and `core`, a
root's `asid`.  A CNode's radix is read below `maxCSpaceDepth`. -/
def CarveRequest.ofWords (k n : Nat) (dom : SeLe4n.DomainId)
    (core : SeLe4n.Kernel.Concurrency.CoreId) (asid : SeLe4n.ASID) : CarveRequest :=
  match k with
  | 0 => .frame
  | 1 => .untyped n
  | 2 => .vspaceRoot asid
  | 3 => .pageTable
  | 4 => .tcb dom core
  | 5 => .endpoint
  | 6 => .notification
  | 7 => .cnode (min n maxCSpaceDepth) (Nat.min_le_right _ _)
  | 8 => .reply
  | _ => .schedContext n

/-- A request's kind code. -/
def CarveRequest.kindWord : CarveRequest → Nat
  | .frame => 0
  | .untyped _ => 1
  | .vspaceRoot _ => 2
  | .pageTable => 3
  | .tcb _ _ => 4
  | .endpoint => 5
  | .notification => 6
  | .cnode _ _ => 7
  | .reply => 8
  | .schedContext _ => 9

/-- A request's size or radix word (`0` for a fixed-size kind). -/
def CarveRequest.sizeWord : CarveRequest → Nat
  | .untyped b => b
  | .cnode r _ => r
  | .schedContext b => b
  | _ => 0

/-- A request's domain word (`dom0` for a kind other than a thread). -/
def CarveRequest.domainWord (dom0 : SeLe4n.DomainId) : CarveRequest → SeLe4n.DomainId
  | .tcb d _ => d
  | _ => dom0

/-- A request's core word (`core0` for a kind other than a thread). -/
def CarveRequest.coreWord (core0 : SeLe4n.Kernel.Concurrency.CoreId) :
    CarveRequest → SeLe4n.Kernel.Concurrency.CoreId
  | .tcb _ c => c
  | _ => core0

/-- A request's ASID word (`asid0` for a kind other than a VSpace root). -/
def CarveRequest.asidWord (asid0 : SeLe4n.ASID) : CarveRequest → SeLe4n.ASID
  | .vspaceRoot a => a
  | _ => asid0

/-- **A request is the request its words name.** -/
theorem CarveRequest.ofWords_words (dom0 : SeLe4n.DomainId)
    (core0 : SeLe4n.Kernel.Concurrency.CoreId) (asid0 : SeLe4n.ASID) (req : CarveRequest) :
    CarveRequest.ofWords req.kindWord req.sizeWord (req.domainWord dom0) (req.coreWord core0)
      (req.asidWord asid0) = req := by
  cases req with
  | cnode r h =>
    simp only [ofWords, kindWord, sizeWord]
    congr 1
    exact Nat.min_eq_left h
  | _ => rfl

/-- `CarveRequest.objectType` of the words. -/
@[inline] def CarveRequest.objectTypeW (k : Nat) : KernelObjectType :=
  match k with
  | 0 => .frame | 1 => .untyped | 2 => .vspaceRoot | 3 => .pageTable | 4 => .tcb
  | 5 => .endpoint | 6 => .notification | 7 => .cnode | 8 => .reply | _ => .schedContext

/-- `CarveRequest.size` of the words. -/
@[inline] def CarveRequest.sizeW (k n : Nat) : Nat :=
  match k with
  | 0 => SeLe4n.pageBytes | 1 => 2 ^ n | 2 => SeLe4n.pageBytes | 3 => SeLe4n.pageBytes
  | 4 => objectTypeAllocSize .tcb | 5 => objectTypeAllocSize .endpoint
  | 6 => objectTypeAllocSize .notification
  | 7 => 2 ^ (min n maxCSpaceDepth + cnodeSlotBits)
  | 8 => objectTypeAllocSize .reply | _ => 2 ^ n

/-- `CarveRequest.rights` of the words. -/
@[inline] def CarveRequest.rightsW (k : Nat) : AccessRightSet :=
  match k with
  | 0 => AccessRightSet.ofList [.read, .write, .grant]
  | 1 => AccessRightSet.ofList [.read, .write, .retype]
  | 2 => AccessRightSet.ofList [.read, .write]
  | 3 => AccessRightSet.ofList [.read, .write]
  | _ => kernelObjectRights

/-- `CarveRequest.objectImpl` of the words: the object built with its cells. -/
@[inline] def CarveRequest.objectW (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject)
    (idx k n : Nat) (dom : SeLe4n.DomainId) (core : SeLe4n.Kernel.Concurrency.CoreId)
    (asid : SeLe4n.ASID) : KernelObject :=
  match k with
  | 0 => .frame (untypedNextFrame ut idx)
  | 1 => .untyped (untypedNextChild ut idx untypedId n)
  | 2 => (KernelObject.vspaceRoot (untypedNextVSpaceRoot ut idx asid)).unshareFresh
  | 3 => .pageTable (untypedNextPageTable ut idx)
  | 4 => (KernelObject.tcb (carvedTcb childId dom core)).unshareFresh
  | 5 => (KernelObject.endpoint (Endpoint.ofQueues {} {})).unshareFresh
  | 6 => (KernelObject.notification ({ state := .idle } : Notification)).unshareFresh
  | 7 => .cnode (carvedCNode (min n maxCSpaceDepth))
  | 8 => .reply (SeLe4n.Kernel.Reply.empty (SeLe4n.ReplyId.ofObjId childId))
  | _ => .schedContext (SeLe4n.Kernel.SchedContext.empty (SeLe4n.SchedContextId.ofObjId childId))

/-- `CarveRequest.scrubAt` of the words. -/
@[inline] def CarveRequest.scrubAtW (st : SystemState) (base : SeLe4n.PAddr) (isDevice : Bool)
    (k : Nat) : SystemState :=
  match k with
  | 0 =>
      if isDevice then st
      else { st with
              machine := SeLe4n.zeroMemoryRange st.machine base SeLe4n.pageBytes
              physicalWrites := st.physicalWrites.pushAfter st.physicalWritesDrained
                (SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage base)
              physicalWritesDrained := false }
  | 2 | 3 =>
      { st with
          machine := SeLe4n.zeroMemoryRange st.machine base SeLe4n.pageBytes
          physicalWrites := st.physicalWrites.pushAfter st.physicalWritesDrained
            (SeLe4n.Kernel.Architecture.PhysicalWrite.zeroPage base)
          physicalWritesDrained := false }
  | _ => st

/-- `CarveRequest.heapAdmitted` of the words. -/
@[inline] def CarveRequest.heapAdmittedW (st : SystemState) (k n : Nat) : Bool :=
  decide (retypeHeapReserveBytes +
      (match k with
       | 2 => carvedVSpaceRootHeapBytes
       | 4 => carvedTcbHeapBytes
       | 7 => carvedObjectHeapBytes + cnodeSlotHeapBytes * 2 ^ (min n maxCSpaceDepth)
       | _ => carvedObjectHeapBytes)
      + rhInsertResizeHeapBytes st.objects
      + (match k with
         | 2 => rhInsertResizeHeapBytes st.asidTable
         | _ => 0) ≤ st.machine.kernelHeapFreeBytes)

/-- `CarveRequest.admissible` of the words. -/
@[inline] def CarveRequest.admissibleW (st : SystemState) (k : Nat) (asid : SeLe4n.ASID) : Bool :=
  match k with
  | 2 =>
      asid.toNat != 0 && decide (asid.toNat < st.machine.maxASID) &&
        (st.asidTable[asid]?).isNone
  | _ => true

section CarveWords
variable (k n : Nat) (dom : SeLe4n.DomainId) (core : SeLe4n.Kernel.Concurrency.CoreId)
  (asid : SeLe4n.ASID)

theorem CarveRequest.objectTypeW_eq :
    CarveRequest.objectTypeW k = (CarveRequest.ofWords k n dom core asid).objectType := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

theorem CarveRequest.sizeW_eq :
    CarveRequest.sizeW k n = (CarveRequest.ofWords k n dom core asid).size := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

theorem CarveRequest.rightsW_eq :
    CarveRequest.rightsW k = (CarveRequest.ofWords k n dom core asid).rights := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

theorem CarveRequest.objectW_eq (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject)
    (idx : Nat) :
    CarveRequest.objectW untypedId childId ut idx k n dom core asid =
      (CarveRequest.ofWords k n dom core asid).object untypedId childId ut idx := by
  rw [CarveRequest.object_eq_impl]
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

theorem CarveRequest.scrubAtW_eq (st : SystemState) (base : SeLe4n.PAddr) (isDevice : Bool) :
    CarveRequest.scrubAtW st base isDevice k =
      (CarveRequest.ofWords k n dom core asid).scrubAt st base isDevice := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

theorem CarveRequest.heapAdmittedW_eq (st : SystemState) :
    CarveRequest.heapAdmittedW st k n = (CarveRequest.ofWords k n dom core asid).heapAdmitted st := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

theorem CarveRequest.admissibleW_eq (st : SystemState) :
    CarveRequest.admissibleW st k asid = (CarveRequest.ofWords k n dom core asid).admissible st := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

end CarveWords

/-- **`untypedRetypePerformWords` read off the request's words**, so no request
is built: the compiled carve's writes. -/
def untypedRetypePerformCode (srcCnode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (dstCnode : SeLe4n.ObjId) (dstSlot : SeLe4n.Slot) (childId : SeLe4n.ObjId)
    (k n : Nat) (dom : SeLe4n.DomainId) (core : SeLe4n.Kernel.Concurrency.CoreId)
    (asid : SeLe4n.ASID) (st : SystemState) : SystemState :=
  match SystemState.lookupSlotCap st ⟨srcCnode, srcSlot⟩ with
  | some utCap =>
    match utCap.target with
    | .object untypedId =>
      match st.getUntyped? untypedId with
      | some ut =>
        let size := CarveRequest.sizeW k n
        let idx := alignedCarveIndex (CarveRequest.objectTypeW k) size ut
          (retypeFreeIndex st ⟨srcCnode, srcSlot⟩ utCap)
        let newObj := CarveRequest.objectW untypedId childId ut idx k n dom core asid
        let base := (untypedNextFrame ut idx).base
        let isDevice := ut.isDevice
        let st1 := st.storeUntypedWith untypedId (·.allocated idx childId size)
        let st2 := storedState childId newObj st1
        let st3 := st2.storeCNodeWith srcCnode (·.setFreeIndexCells srcSlot (idx + size))
        ((CarveRequest.scrubAtW st3 base isDevice k).storeCNodeWith dstCnode
          (·.insertObjectCap dstSlot childId (CarveRequest.rightsW k))).cdtAddChild
            ⟨srcCnode, srcSlot⟩ ⟨dstCnode, dstSlot⟩ .retype
      | none => st
    | _ => st
  | none => st

theorem untypedRetypePerformCode_eq_words (srcCnode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (dstCnode : SeLe4n.ObjId) (dstSlot : SeLe4n.Slot) (childId : SeLe4n.ObjId)
    (k n : Nat) (dom : SeLe4n.DomainId) (core : SeLe4n.Kernel.Concurrency.CoreId)
    (asid : SeLe4n.ASID) (st : SystemState) :
    untypedRetypePerformCode srcCnode srcSlot dstCnode dstSlot childId k n dom core asid st =
      untypedRetypePerformWords srcCnode srcSlot dstCnode dstSlot childId
        (CarveRequest.ofWords k n dom core asid) st := by
  unfold untypedRetypePerformCode untypedRetypePerformWords
  simp only [CarveRequest.carveIndex, ← CarveRequest.objectTypeW_eq k n dom core asid,
    ← CarveRequest.sizeW_eq k n dom core asid, ← CarveRequest.objectW_eq k n dom core asid,
    ← CarveRequest.scrubAtW_eq k n dom core asid, ← CarveRequest.rightsW_eq k n dom core asid]

/-- **The compiled carve's writes are the carve's**, given the request's
words. -/
theorem untypedRetypePerformCode_eq (src dst : CSpaceAddr) (childId : SeLe4n.ObjId)
    (dom0 : SeLe4n.DomainId) (core0 : SeLe4n.Kernel.Concurrency.CoreId) (asid0 : SeLe4n.ASID)
    (req : CarveRequest) (st : SystemState) :
    untypedRetypePerformCode src.cnode src.slot dst.cnode dst.slot childId req.kindWord
        req.sizeWord (req.domainWord dom0) (req.coreWord core0) (req.asidWord asid0) st =
      untypedRetypePerformAt src dst childId req st := by
  rw [untypedRetypePerformCode_eq_words, CarveRequest.ofWords_words, untypedRetypePerformAt_eq_words]

/-- **`untypedRetypeAdmittedAt` read off the request's words.** -/
@[inline] def untypedRetypeAdmittedCode (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (k n : Nat) (asid : SeLe4n.ASID) : Bool :=
  CarveRequest.heapAdmittedW st k n && CarveRequest.admissibleW st k asid &&
  match SystemState.lookupSlotCap st src with
  | some utCap =>
    match utCap.target with
    | .object untypedId =>
      match st.getUntyped? untypedId with
      | some ut =>
        cspaceDstAdmitted dst st &&
        retypeFromUntypedAdmitted st src.cnode src.slot utCap untypedId childId
          (CarveRequest.objectTypeW k) (CarveRequest.sizeW k n) ut
      | none => false
    | _ => false
  | none => false

theorem untypedRetypeAdmittedCode_eq (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (dom0 : SeLe4n.DomainId) (core0 : SeLe4n.Kernel.Concurrency.CoreId)
    (asid0 : SeLe4n.ASID) (req : CarveRequest) :
    untypedRetypeAdmittedCode st src dst childId req.kindWord req.sizeWord (req.asidWord asid0) =
      untypedRetypeAdmittedAt st src dst childId req := by
  conv => rhs; rw [← CarveRequest.ofWords_words dom0 core0 asid0 req]
  unfold untypedRetypeAdmittedCode untypedRetypeAdmittedAt
  simp only [← CarveRequest.heapAdmittedW_eq req.kindWord req.sizeWord (req.domainWord dom0)
      (req.coreWord core0) (req.asidWord asid0),
    ← CarveRequest.admissibleW_eq req.kindWord req.sizeWord (req.domainWord dom0)
      (req.coreWord core0) (req.asidWord asid0),
    ← CarveRequest.objectTypeW_eq req.kindWord req.sizeWord (req.domainWord dom0)
      (req.coreWord core0) (req.asidWord asid0),
    ← CarveRequest.sizeW_eq req.kindWord req.sizeWord (req.domainWord dom0)
      (req.coreWord core0) (req.asidWord asid0)]

/-- **`untypedRetypeRefusalWith` read off the request's words.** -/
@[inline] def untypedRetypeRefusalCode (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (k n : Nat) (asid : SeLe4n.ASID) : KernelError :=
  untypedRetypeRefusalWith st src dst childId (CarveRequest.heapAdmittedW st k n)
    (CarveRequest.admissibleW st k asid) (CarveRequest.objectTypeW k) (CarveRequest.sizeW k n)

theorem untypedRetypeRefusalCode_eq (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (dom0 : SeLe4n.DomainId) (core0 : SeLe4n.Kernel.Concurrency.CoreId)
    (asid0 : SeLe4n.ASID) (req : CarveRequest) :
    untypedRetypeRefusalCode st src dst childId req.kindWord req.sizeWord (req.asidWord asid0) =
      untypedRetypeRefusalWith st src dst childId (req.heapAdmitted st) (req.admissible st)
        req.objectType req.size := by
  conv => rhs; rw [← CarveRequest.ofWords_words dom0 core0 asid0 req]
  unfold untypedRetypeRefusalCode
  rw [CarveRequest.heapAdmittedW_eq req.kindWord req.sizeWord (req.domainWord dom0)
      (req.coreWord core0) (req.asidWord asid0),
    CarveRequest.admissibleW_eq req.kindWord req.sizeWord (req.domainWord dom0)
      (req.coreWord core0) (req.asidWord asid0),
    CarveRequest.objectTypeW_eq req.kindWord req.sizeWord (req.domainWord dom0)
      (req.coreWord core0) (req.asidWord asid0),
    CarveRequest.sizeW_eq req.kindWord req.sizeWord (req.domainWord dom0)
      (req.coreWord core0) (req.asidWord asid0)]

/-- The carve's heap check, read off the request's words. -/
theorem CarveRequest.heapAdmittedW_words (st : SystemState) (dom0 : SeLe4n.DomainId)
    (core0 : SeLe4n.Kernel.Concurrency.CoreId) (asid0 : SeLe4n.ASID) (req : CarveRequest) :
    CarveRequest.heapAdmittedW st req.kindWord req.sizeWord = req.heapAdmitted st := by
  rw [CarveRequest.heapAdmittedW_eq req.kindWord req.sizeWord (req.domainWord dom0)
    (req.coreWord core0) (req.asidWord asid0), CarveRequest.ofWords_words]
