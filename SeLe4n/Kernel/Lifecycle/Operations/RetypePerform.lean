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
`untypedId`, the authority capability `authCap` already read, read before any
write; the carve is at `authCap`'s free index.  The new object enters as its
type `ty` alone, so the check builds no object. -/
def retypeFromUntypedAdmitted (st : SystemState) (authCap : Capability)
    (untypedId childId : SeLe4n.ObjId) (ty : KernelObjectType) (size : Nat)
    (ut : UntypedObject) : Bool :=
  !decide (st.objectIndex.length ≥ maxObjects) &&
  !decide (childId = untypedId) &&
  !(st.getObject? childId).isSome &&
  childrenNameNone childId ut.children &&
  !(ut.isDevice && !ty.deviceBackable) &&
  objectIdInAddressSpace st.machine childId &&
  !decide (size < objectTypeAllocSize ty) &&
  !(requiresPageAlignment ty && !allocationBasePageAligned ut authCap.freeIndex) &&
  lifecycleRetypeAuthority authCap untypedId &&
  ut.canAllocate authCap.freeIndex size &&
  !(requiresPageAlignment ty && !allocationBasePageAligned ut (authCap.freeIndex + size))

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
    (hA : retypeFromUntypedAdmitted st authCap untypedId childId newObj.objectType size ut = true) :
    retypeFromUntyped authority untypedId childId newObj size st =
      .ok ((), retypeFromUntypedWrites authority authCap.freeIndex untypedId childId newObj size ut
        st) := by
  unfold retypeFromUntypedAdmitted at hA
  rw [childrenNameNone_eq] at hA
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hA
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hCap, hSelf⟩, hFresh⟩, hKids⟩, hDev⟩, hAddr⟩, hSize⟩, hAl⟩, hAuth⟩,
    hCan⟩, hAl'⟩ := hA
  have hLkS : cspaceLookupSlot authority st = .ok (authCap, st) := by
    unfold cspaceLookupSlot; rw [hLk]
  unfold retypeFromUntyped
  simp only [hUt, hCap, hSelf, hFresh, hKids, hDev, hAddr, hSize, hAl, hLkS, hAuth,
    UntypedObject.allocate_eq_allocated ut authCap.freeIndex childId size hCan, hAl', ↓reduceIte,
    Bool.false_eq_true, storeObject_eq_storedState]
  rfl

/-- WS-ZA ZA5.4: **every refusal of `untypedRetypeObject`**, read from the state
it is handed: the request's own precondition, the untyped capability in `src`
naming an untyped, the destination slot, and the carve's checks. -/
@[inline] def untypedRetypeAdmittedAt (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (req : CarveRequest) : Bool :=
  req.admissible st &&
  match SystemState.lookupSlotCap st src with
  | some utCap =>
    match utCap.target with
    | .object untypedId =>
      match st.getUntyped? untypedId with
      | some ut =>
        cspaceDstAdmitted dst st &&
        retypeFromUntypedAdmitted st utCap untypedId childId req.objectType req.size ut
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
        let st1 := retypeFromUntypedWrites src utCap.freeIndex untypedId childId
          (req.object untypedId ut utCap.freeIndex) req.size ut st
        ((req.scrub st1 ut utCap.freeIndex).storeCNodeWith dst.cnode
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
  obtain ⟨hAdm, hRest⟩ := hA
  unfold untypedRetypeObject untypedRetypePerformAt
  simp only [hAdm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
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
        dsimp only
        rw [(cspaceDstRefusal_eq_ok_iff dst st).mpr hD]
        dsimp only
        rw [← CarveRequest.object_objectType untypedId ut utCap.freeIndex] at hR
        rw [retypeFromUntyped_of_admitted hL hUt hR]
    | _ => rw [hT] at hRest; cases hRest

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
        let idx := utCap.freeIndex
        let newObj := req.object untypedId ut idx
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

/-- `untypedRetypePerformAt` as compiled: the slots handed on as words to
`untypedRetypePerformWords`, out of line, where the destination CNode's write is
specialised to its function (no closure is built for it). -/
@[inline] def untypedRetypePerformImpl (src dst : CSpaceAddr) (childId : SeLe4n.ObjId)
    (req : CarveRequest) (st : SystemState) : SystemState :=
  untypedRetypePerformWords src.cnode src.slot dst.cnode dst.slot childId req st

@[csimp] theorem untypedRetypePerformAt_eq_impl :
    @untypedRetypePerformAt = @untypedRetypePerformImpl := by
  funext src dst childId req st
  obtain ⟨sc, ss⟩ := src
  obtain ⟨dc, ds⟩ := dst
  unfold untypedRetypePerformAt untypedRetypePerformImpl untypedRetypePerformWords
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
          (·.allocated utCap.freeIndex childId req.size)
        rw [setCapFreeIndex_eq_impl]
        unfold setCapFreeIndexImpl
        have hF : ∀ cn : CNode, cn.insertObjectCap ds childId req.rights =
            cn.insert ds (req.capability childId) := by
          intro cn; rw [CNode.insertObjectCap_eq_insert, CarveRequest.capability_eq]
        simp only [storedState, hS, hF]
    · rfl
  · rfl
