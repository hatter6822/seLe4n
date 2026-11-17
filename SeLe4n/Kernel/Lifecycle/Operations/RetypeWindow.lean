-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.RetypePerform

/-!
# The retype window: `count` objects in one `seL4_Untyped_Retype`

WS-SX SX6.3 (D9): seL4's `Untyped_Retype` creates up to
`CONFIG_RETYPE_FAN_OUT_LIMIT` objects of one kind in one call.  Object `i` takes
the window's slot `offset + i` (`retypeChildSlot`) and, in the model, the
object id `childId + i` (`retypeChildId`, the id the lock footprint names for
it, `carvedChildLocks`).

seL4 splits the call into `decodeUntypedInvocation`, which checks everything,
and `invokeUntyped`, which cannot fail.  The model splits it the same way:
`untypedRetypeWindowRefusal` is every check, read from the state the call is
handed, in seL4's order — every slot of the window empty, then the region
holding all `count` objects — and then the model's own checks of all `count`
ids, of the object store's capacity, of the VSpace roots' ASIDs and of the
kernel heap; `untypedRetypeWindowWrites` is the carves, one
`untypedRetypePerformAt` per object.  Each carve still reads its own admission
(`untypedRetypeAdmittedAt`) before it writes, so every write the window makes is
a successful `untypedRetypeObject` (`untypedRetypeWindowWrites_chain`); under
the store's table invariants an admitted window admits every carve
(`untypedRetypeWindow_admitsEveryCarve`), so the window either refuses before
any write and returns the state it was handed, or makes all `count` objects.

Only the first carve may reset the untyped: it leaves a derivation child in the
invoked capability's slot, so every later carve starts at the capability's free
index (`retypeFreeIndex`), as seL4 lays the objects out one after another from
`alignUp(freeRef, objectSize)`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- The window's objects
-- ============================================================================

/-- **The id of object `i` of a window** whose first object takes `childId`:
`childId + i`, the id the carve's lock footprint names for it
(`carvedChildLocks`). -/
@[inline] def retypeChildId (childId : SeLe4n.ObjId) (i : Nat) : SeLe4n.ObjId :=
  SeLe4n.ObjId.ofNat (childId.toNat + i)

/-- **The slot of object `i` of a window** whose first slot is `dst`: slot
`offset + i` of the same CNode, as seL4's `invokeUntyped_Retype` fills
`destSlots[i]`. -/
@[inline] def retypeChildSlot (dst : CSpaceAddr) (i : Nat) : CSpaceAddr :=
  { cnode := dst.cnode, slot := SeLe4n.Slot.ofNat (dst.slot.toNat + i) }

@[simp] theorem retypeChildId_zero (childId : SeLe4n.ObjId) : retypeChildId childId 0 = childId :=
  rfl

@[simp] theorem retypeChildSlot_zero (dst : CSpaceAddr) : retypeChildSlot dst 0 = dst := rfl

/-- WS-ZA ZA6.35: `freshAsidFrom` as a code: `0` for no ASID, `a + 1` for
ASID `a`, so the scan builds no `some`. -/
def freshAsidCodeFrom (st : SystemState) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
      if n < st.machine.maxASID then
        if (st.asidTable[SeLe4n.ASID.ofNat n]?).isNone then n + 1
        else freshAsidCodeFrom st fuel (n + 1)
      else 0

theorem freshAsidFrom_eq_code (st : SystemState) : ∀ (fuel n : Nat),
    freshAsidFrom st fuel n =
      match freshAsidCodeFrom st fuel n with
      | 0 => none
      | a + 1 => some (SeLe4n.ASID.ofNat a)
  | 0, _ => rfl
  | fuel + 1, n => by
    unfold freshAsidFrom freshAsidCodeFrom
    split
    · split
      · rfl
      · exact freshAsidFrom_eq_code st fuel (n + 1)
    · rfl

/-- **The request a window's carve makes at the state it is carved in.**  A
VSpace root takes the least ASID free there (`freshAsid?`): each root's carve
inserts its own ASID, so the roots of one window take the window's `count`
least free ASIDs in turn, which `CarveRequest.windowAdmissible` checks exist
before any write.  Every other kind is carved as it was requested. -/
def CarveRequest.atState (st : SystemState) : CarveRequest → CarveRequest
  | .vspaceRoot a => .vspaceRoot ((freshAsid? st).getD a)
  | r => r

/-- `CarveRequest.atState`'s ASID, read off the words: the least free ASID for
a VSpace root (kind `2`), the word handed in otherwise. -/
@[inline] def CarveRequest.asidAtW (st : SystemState) (k : Nat) (asid : SeLe4n.ASID) :
    SeLe4n.ASID :=
  match k with
  | 2 =>
      match freshAsidCodeFrom st st.machine.maxASID 1 with
      | 0 => asid
      | a + 1 => SeLe4n.ASID.ofNat a
  | _ => asid

theorem CarveRequest.ofWords_asidAtW (st : SystemState) (k n : Nat) (dom : SeLe4n.DomainId)
    (core : SeLe4n.Kernel.Concurrency.CoreId) (asid : SeLe4n.ASID) :
    CarveRequest.ofWords k n dom core (CarveRequest.asidAtW st k asid) =
      (CarveRequest.ofWords k n dom core asid).atState st := by
  match k with
  | 2 =>
    simp only [CarveRequest.asidAtW, CarveRequest.ofWords, CarveRequest.atState, freshAsid?,
      freshAsidFrom_eq_code st st.machine.maxASID 1]
    split <;> rfl
  | 0 | 1 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

/-- **Are `need` ASIDs free from `n` on?**  The scan `freshAsidFrom` makes,
counting: one step of fuel per ASID, each free ASID below the machine's bound
counted until `need` are found. -/
def freshAsidsFrom (st : SystemState) : Nat → Nat → Nat → Bool
  | _, _, 0 => true
  | 0, _, _ + 1 => false
  | fuel + 1, n, need + 1 =>
      if n < st.machine.maxASID then
        if (st.asidTable[SeLe4n.ASID.ofNat n]?).isNone then freshAsidsFrom st fuel (n + 1) need
        else freshAsidsFrom st fuel (n + 1) (need + 1)
      else false

/-- **Whether the ASID table holds an ASID for every VSpace root of a window of
`count`**: `count` free ASIDs, the ones the roots take in turn
(`CarveRequest.atState`).  Every other kind needs none.  The model's own
check: seL4 assigns a root its ASID later, through an ASID pool. -/
def CarveRequest.windowAdmissible (st : SystemState) (count : Nat) : CarveRequest → Bool
  | .vspaceRoot _ => freshAsidsFrom st st.machine.maxASID 1 count
  | _ => true

-- ============================================================================
-- The kernel heap a window takes
-- ============================================================================

/-- **The heap the resizes of a Robin Hood table take over `inserts` new keys**,
over-approximated from its size `size` and capacity `capacity`: a carve's
writes resize the table at most once, when the load after its new key reaches
the insert's 75% check, and a resize doubles the table
(`rhInsertResizeHeapBytes`). -/
def rhWindowResizeHeapBytes : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | size, capacity, inserts + 1 =>
      if (size + 1) * 4 ≥ capacity * 3 then
        capacity * 2 * rhSlotHeapBytes + rhWindowResizeHeapBytes (size + 1) (capacity * 2) inserts
      else rhWindowResizeHeapBytes (size + 1) capacity inserts

/-- **What a window of `count` objects needs of the kernel heap**,
over-approximated once for all of them: the reserve, `count` carved objects,
and the resizes of the object table over `count` new objects — and of the ASID
table over `count` new ASIDs for VSpace roots.  It is at least what each carve
of the window asks (`CarveRequest.heapBytes`), so the heap admits every carve
of an admitted window. -/
def CarveRequest.windowHeapBytes (st : SystemState) (req : CarveRequest) (count : Nat) : Nat :=
  retypeHeapReserveBytes + count * req.objectHeapBytes
    + rhWindowResizeHeapBytes st.objects.size st.objects.capacity count
    + (match req with
       | .vspaceRoot _ => rhWindowResizeHeapBytes st.asidTable.size st.asidTable.capacity count
       | _ => 0)

/-- `CarveRequest.objectHeapBytes` of the words. -/
@[inline] def CarveRequest.objectHeapBytesW (k n : Nat) : Nat :=
  match k with
  | 2 => carvedVSpaceRootHeapBytes
  | 4 => carvedTcbHeapBytes
  | 7 => carvedObjectHeapBytes + cnodeSlotHeapBytes * 2 ^ (min n maxCSpaceDepth)
  | _ => carvedObjectHeapBytes

/-- `CarveRequest.windowHeapBytes` of the words. -/
@[inline] def CarveRequest.windowHeapBytesW (st : SystemState) (k n count : Nat) : Nat :=
  retypeHeapReserveBytes + count * CarveRequest.objectHeapBytesW k n
    + rhWindowResizeHeapBytes st.objects.size st.objects.capacity count
    + (match k with
       | 2 => rhWindowResizeHeapBytes st.asidTable.size st.asidTable.capacity count
       | _ => 0)

/-- `CarveRequest.windowAdmissible` of the words. -/
@[inline] def CarveRequest.windowAdmissibleW (st : SystemState) (k count : Nat) : Bool :=
  match k with
  | 2 => freshAsidsFrom st st.machine.maxASID 1 count
  | _ => true

theorem CarveRequest.windowHeapBytesW_eq (st : SystemState) (k n count : Nat)
    (dom : SeLe4n.DomainId) (core : SeLe4n.Kernel.Concurrency.CoreId) (asid : SeLe4n.ASID) :
    CarveRequest.windowHeapBytesW st k n count =
      (CarveRequest.ofWords k n dom core asid).windowHeapBytes st count := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

theorem CarveRequest.windowAdmissibleW_eq (st : SystemState) (k n count : Nat)
    (dom : SeLe4n.DomainId) (core : SeLe4n.Kernel.Concurrency.CoreId) (asid : SeLe4n.ASID) :
    CarveRequest.windowAdmissibleW st k count =
      (CarveRequest.ofWords k n dom core asid).windowAdmissible st count := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

-- ============================================================================
-- Every check of the window, before any write
-- ============================================================================

/-- **The first refusal of the window's slots** `i, i + 1, …` (`k` of them) in
the CNode `dstCnode` from slot `dstSlot`: each an addressable, empty slot
(`cspaceDstRefusal`, read inlined as `untypedRetypeDstRefusal` so no slot
reference is built), as seL4's `decodeUntypedInvocation` asks `ensureEmptySlot`
of every slot before it reads the untyped (`seL4_DeleteFirst`). -/
def retypeWindowSlotsRefusal (st : SystemState) (dstCnode : SeLe4n.ObjId) (dstSlot : SeLe4n.Slot) :
    Nat → Nat → Option KernelError
  | _, 0 => none
  | i, k + 1 =>
    match untypedRetypeDstRefusal ⟨dstCnode, SeLe4n.Slot.ofNat (dstSlot.toNat + i)⟩ st with
    | .error e => some e
    | .ok () => retypeWindowSlotsRefusal st dstCnode dstSlot (i + 1) k

/-- The window's slot refusal is `cspaceDstRefusal` of each slot in turn. -/
theorem retypeWindowSlotsRefusal_eq (st : SystemState) (dst : CSpaceAddr) (i k : Nat) :
    retypeWindowSlotsRefusal st dst.cnode dst.slot i (k + 1) =
      match cspaceDstRefusal (retypeChildSlot dst i) st with
      | .error e => some e
      | .ok () => retypeWindowSlotsRefusal st dst.cnode dst.slot (i + 1) k := by
  rw [retypeWindowSlotsRefusal, untypedRetypeDstRefusal_eq]; rfl

/-- **The first refusal of the window's object ids** `i, i + 1, …` (`k` of
them), `retypeFromUntyped`'s checks of each: not the untyped's own id, held by
no object, no interrupt node's reserved id and no child the untyped records,
and inside the machine's physical address space. -/
def retypeWindowIdsRefusal (st : SystemState) (untypedId childId : SeLe4n.ObjId)
    (ut : UntypedObject) : Nat → Nat → Option KernelError
  | _, 0 => none
  | i, k + 1 =>
    if retypeChildId childId i = untypedId then some .childIdSelfOverwrite
    else if (st.getObject? (retypeChildId childId i)).isSome ||
        isIrqNodeObjId InterruptLineSet.capacity (retypeChildId childId i) ||
        !childrenNameNone (retypeChildId childId i) ut.children then some .childIdCollision
    else if !objectIdInAddressSpace st.machine (retypeChildId childId i) then
      some .addressOutOfBounds
    else retypeWindowIdsRefusal st untypedId childId ut (i + 1) k

/-- **Every refusal of a window of `count` objects of kind `ty` and `size`
bytes**, read from the state it is handed, before any write: the invoked
capability (an untyped, named with `.retype`), then seL4's checks in seL4's
order — every slot of the window empty, then the untyped (the reset's own
refusal, the region holding all `count` objects from the rounded free index,
`seL4_NotEnoughMemory`, and the device rule) — then the model's: every object
id, the object store's capacity for `count` more objects, the VSpace roots'
ASIDs (`asidsOk`) and the kernel heap for all of them (`heapOk`).
`none` is an admitted window. -/
@[inline] def untypedRetypeWindowRefusalWith (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (ty : KernelObjectType) (size : Nat) (asidsOk heapOk : Bool)
    (count : Nat) : Option KernelError :=
  match SystemState.lookupSlotCap st src with
  | none =>
    match st.getCNode? src.cnode with
    | some _ => some (.invalidCapability 0)
    | none => some .objectNotFound
  | some utCap =>
    match utCap.target with
    | .object untypedId =>
      if !lifecycleRetypeAuthority utCap untypedId then some .illegalAuthority else
      match st.getUntyped? untypedId with
      | none => some .untypedTypeMismatch
      | some ut =>
        match retypeWindowSlotsRefusal st dst.cnode dst.slot 0 count with
        | some e => some e
        | none =>
          if !retypeResetAdmitted st src ut then some .revocationRequired
          else if !ut.canAllocate (alignedCarveIndex ty size ut (retypeFreeIndex st src utCap))
              (count * size) then
            some (.untypedRegionExhausted (ut.regionSize - retypeFreeIndex st src utCap).toUInt64)
          else if ut.isDevice && !ty.deviceBackable then some .untypedDeviceRestriction
          else if size < objectTypeAllocSize ty then some .untypedAllocSizeTooSmall
          else
            match retypeWindowIdsRefusal st untypedId childId ut 0 count with
            | some e => some e
            | none =>
              if maxObjects < st.objects.size + count then some .objectStoreCapacityExceeded
              else if !asidsOk then some .resourceExhausted
              else if !heapOk then
                some (.untypedRegionExhausted st.machine.kernelHeapFreeBytes.toUInt64)
              else none
    | _ => some (.invalidCapability 0)

/-- **Every refusal of a window of `count` objects `req` names**
(`untypedRetypeWindowRefusalWith` at the request's kind and size, its ASIDs and
its heap). -/
def untypedRetypeWindowRefusal (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (req : CarveRequest) (count : Nat) : Option KernelError :=
  untypedRetypeWindowRefusalWith st src dst childId req.objectType req.size
    (req.windowAdmissible st count)
    (decide (req.windowHeapBytes st count ≤ st.machine.kernelHeapFreeBytes)) count

/-- `untypedRetypeWindowRefusal` read off the request's words. -/
@[inline] def untypedRetypeWindowRefusalCode (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (k n count : Nat) : Option KernelError :=
  untypedRetypeWindowRefusalWith st src dst childId (CarveRequest.objectTypeW k)
    (CarveRequest.sizeW k n) (CarveRequest.windowAdmissibleW st k count)
    (decide (CarveRequest.windowHeapBytesW st k n count ≤ st.machine.kernelHeapFreeBytes)) count

theorem untypedRetypeWindowRefusalCode_eq (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (k n count : Nat) (dom : SeLe4n.DomainId)
    (core : SeLe4n.Kernel.Concurrency.CoreId) (asid : SeLe4n.ASID) :
    untypedRetypeWindowRefusalCode st src dst childId k n count =
      untypedRetypeWindowRefusal st src dst childId (CarveRequest.ofWords k n dom core asid)
        count := by
  unfold untypedRetypeWindowRefusalCode untypedRetypeWindowRefusal
  rw [CarveRequest.objectTypeW_eq k n dom core asid, CarveRequest.sizeW_eq k n dom core asid,
    CarveRequest.windowAdmissibleW_eq st k n count dom core asid,
    CarveRequest.windowHeapBytesW_eq st k n count dom core asid]

-- ============================================================================
-- The carves
-- ============================================================================

/-- **The window's carves** `i, i + 1, …` (`k` of them), seL4's
`invokeUntyped_Retype`: object `i` carved at the state the carves before it
left (`untypedRetypePerformAt` of `req.atState`), its id `retypeChildId` and its
slot `retypeChildSlot`.  Each carve reads its own admission
(`untypedRetypeAdmittedAt`) before it writes, so every carve made is a
successful `untypedRetypeObject`; a carve not admitted ends the window where it
stands, which an admitted window never reaches under the store's table
invariants (`untypedRetypeWindow_admitsEveryCarve`). -/
def untypedRetypeWindowWrites (src dst : CSpaceAddr) (childId : SeLe4n.ObjId)
    (req : CarveRequest) : Nat → Nat → SystemState → SystemState
  | _, 0, st => st
  | i, k + 1, st =>
    if untypedRetypeAdmittedAt st src (retypeChildSlot dst i) (retypeChildId childId i)
        (req.atState st) then
      untypedRetypeWindowWrites src dst childId req (i + 1) k
        (untypedRetypePerformAt src (retypeChildSlot dst i) (retypeChildId childId i)
          (req.atState st) st)
    else st

/-- **WS-SX SX6.3 (D9): a window of `count` objects carved out of the untyped
the capability in `src` names — seL4's `seL4_Untyped_Retype`.**  Every refusal
first (`untypedRetypeWindowRefusal`), read from the state the call is handed, so
a refused window writes nothing; then the carves
(`untypedRetypeWindowWrites`), object `i` at id `childId + i` into slot
`dst + i`. -/
def untypedRetypeWindow (src : CSpaceAddr) (childId : SeLe4n.ObjId) (dst : CSpaceAddr)
    (req : CarveRequest) (count : Nat) : Kernel Unit :=
  fun st =>
    match untypedRetypeWindowRefusal st src dst childId req count with
    | some e => .error e
    | none => .ok ((), untypedRetypeWindowWrites src dst childId req 0 count st)

/-- **A chain of successful carves** from one state to another: what a window
writes (`untypedRetypeWindowWrites_chain`).  An invariant every single carve
keeps is kept by the chain (`RetypeCarveChain.preserves`). -/
inductive RetypeCarveChain : SystemState → SystemState → Prop
  | done (st : SystemState) : RetypeCarveChain st st
  | carve {st st1 st' : SystemState} (src dst : CSpaceAddr) (childId : SeLe4n.ObjId)
      (req : CarveRequest) (h : untypedRetypeObject src childId dst req st = .ok ((), st1))
      (rest : RetypeCarveChain st1 st') : RetypeCarveChain st st'

/-- **A carve keeps the object table well formed**: its stores, the scrub
(which moves no object), the capability's insert and the derivation edge each
do. -/
theorem untypedRetypeObject_preserves_objects_invExt {src dst : CSpaceAddr}
    {childId : SeLe4n.ObjId} {req : CarveRequest} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    st'.objects.invExt := by
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hInv hStep
  obtain ⟨_, _, _, stUt, _, stCh, _, _, _, _, _, _, _, _, _, _, _, hStUt, hStCh, _, hStIdx⟩ :=
    retypeFromUntyped_ok_stores st st1 src untypedId childId _ _ hInv hRt
  have hInvUt := storeObject_preserves_objects_invExt _ _ _ _ hInv hStUt
  have hInvCh := storeObject_preserves_objects_invExt _ _ _ _ hInvUt hStCh
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInvCh hStIdx
  have hInvZ : (req.scrub st1 ut (req.carveIndex ut (retypeFreeIndex st src utCap))).objects.invExt := by
    rw [CarveRequest.scrub_objects]; exact hInv1
  exact (SystemState.cdtAddChild_agreeObjects (cspaceInsertSlot_preserves_objects_invExt _ _ _ _ hInvZ hIns)
    _ _ _).2

/-- **What every single carve does, the chain does**: a relation that is
reflexive and transitive and holds across each successful carve from a state
satisfying `P`, where every carve keeps `P`, holds across the chain. -/
theorem RetypeCarveChain.rel {P : SystemState → Prop} {R : SystemState → SystemState → Prop}
    (hRefl : ∀ s, R s s) (hTrans : ∀ {a b c}, R a b → R b c → R a c)
    (hKeep : ∀ {src dst childId req s s1}, P s →
      untypedRetypeObject src childId dst req s = .ok ((), s1) → P s1)
    (hStep : ∀ {src dst childId req s s1}, P s →
      untypedRetypeObject src childId dst req s = .ok ((), s1) → R s s1)
    {st st' : SystemState} (h : RetypeCarveChain st st') (hP : P st) : R st st' := by
  induction h with
  | done s => exact hRefl s
  | carve src dst childId req hC _ ih => exact hTrans (hStep hP hC) (ih (hKeep hP hC))

/-- **An invariant every single carve keeps, the chain keeps.** -/
theorem RetypeCarveChain.preserves {P : SystemState → Prop}
    (hKeep : ∀ {src dst childId req s s1}, P s →
      untypedRetypeObject src childId dst req s = .ok ((), s1) → P s1)
    {st st' : SystemState} (h : RetypeCarveChain st st') (hP : P st) : P st' := by
  induction h with
  | done _ => exact hP
  | carve _ _ _ _ hC _ ih => exact ih (hKeep hP hC)

/-- **Every write a window makes is a successful carve.** -/
theorem untypedRetypeWindowWrites_chain (src dst : CSpaceAddr) (childId : SeLe4n.ObjId)
    (req : CarveRequest) : ∀ (i k : Nat) (st : SystemState),
    RetypeCarveChain st (untypedRetypeWindowWrites src dst childId req i k st)
  | _, 0, st => .done st
  | i, k + 1, st => by
    unfold untypedRetypeWindowWrites
    split
    · next hA =>
      exact .carve src (retypeChildSlot dst i) (retypeChildId childId i) (req.atState st)
        (untypedRetypeObject_of_admitted hA)
        (untypedRetypeWindowWrites_chain src dst childId req (i + 1) k _)
    · exact .done st

/-- **A successful window is a refusal-free check and a chain of successful
carves.** -/
theorem untypedRetypeWindow_ok {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {count : Nat} {st st' : SystemState}
    (h : untypedRetypeWindow src childId dst req count st = .ok ((), st')) :
    untypedRetypeWindowRefusal st src dst childId req count = none ∧
      RetypeCarveChain st st' := by
  unfold untypedRetypeWindow at h
  cases hR : untypedRetypeWindowRefusal st src dst childId req count with
  | some e => rw [hR] at h; cases h
  | none =>
    rw [hR] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    subst h
    exact ⟨rfl, untypedRetypeWindowWrites_chain src dst childId req 0 count st⟩

-- ============================================================================
-- The window as compiled
-- ============================================================================

/-- `untypedRetypeAdmittedCode` is the admission of the request its words name. -/
theorem untypedRetypeAdmittedCode_eq_ofWords (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (k n : Nat) (dom : SeLe4n.DomainId)
    (core : SeLe4n.Kernel.Concurrency.CoreId) (asid : SeLe4n.ASID) :
    untypedRetypeAdmittedCode st src dst childId k n asid =
      untypedRetypeAdmittedAt st src dst childId (CarveRequest.ofWords k n dom core asid) := by
  unfold untypedRetypeAdmittedCode untypedRetypeAdmittedAt
  rw [CarveRequest.heapAdmittedW_eq k n dom core asid, CarveRequest.admissibleW_eq k n dom core asid,
    CarveRequest.objectTypeW_eq k n dom core asid, CarveRequest.sizeW_eq k n dom core asid]

/-- **The window's carves as compiled**: `untypedRetypeWindowWrites` read off
the request's words — the kind `k`, the size `n`, a thread's domain and core
and a root's ASID word — with each slot and id as words, each carve's
admission and writes the single carve's compiled forms
(`untypedRetypeAdmittedCode`, `untypedRetypePerformCode`), and a root's ASID
the least free one at the state it is carved in (`CarveRequest.asidAtW`).  It
builds no request, slot reference or list: each carve allocates only what its
own object and capability take (`untypedRetypeWindowCode_eq`). -/
def untypedRetypeWindowCode (srcCnode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (dstCnode : SeLe4n.ObjId) (dstSlot : SeLe4n.Slot) (childId : SeLe4n.ObjId)
    (k n : Nat) (dom : SeLe4n.DomainId) (core : SeLe4n.Kernel.Concurrency.CoreId)
    (asid : SeLe4n.ASID) : Nat → Nat → SystemState → SystemState
  | _, 0, st => st
  | i, c + 1, st =>
    if untypedRetypeAdmittedCode st ⟨srcCnode, srcSlot⟩
        ⟨dstCnode, SeLe4n.Slot.ofNat (dstSlot.toNat + i)⟩ (SeLe4n.ObjId.ofNat (childId.toNat + i))
        k n (CarveRequest.asidAtW st k asid) then
      untypedRetypeWindowCode srcCnode srcSlot dstCnode dstSlot childId k n dom core asid
        (i + 1) c
        (untypedRetypePerformCode srcCnode srcSlot dstCnode (SeLe4n.Slot.ofNat (dstSlot.toNat + i))
          (SeLe4n.ObjId.ofNat (childId.toNat + i)) k n dom core (CarveRequest.asidAtW st k asid) st)
    else st

/-- **The compiled carves are the window's.** -/
theorem untypedRetypeWindowCode_eq_ofWords (src dst : CSpaceAddr) (childId : SeLe4n.ObjId)
    (k n : Nat) (dom : SeLe4n.DomainId) (core : SeLe4n.Kernel.Concurrency.CoreId)
    (asid : SeLe4n.ASID) : ∀ (i c : Nat) (st : SystemState),
    untypedRetypeWindowCode src.cnode src.slot dst.cnode dst.slot childId k n dom core asid i c st =
      untypedRetypeWindowWrites src dst childId (CarveRequest.ofWords k n dom core asid) i c st
  | _, 0, _ => rfl
  | i, c + 1, st => by
    unfold untypedRetypeWindowCode untypedRetypeWindowWrites
    have hA := untypedRetypeAdmittedCode_eq_ofWords st src (retypeChildSlot dst i)
      (retypeChildId childId i) k n dom core (CarveRequest.asidAtW st k asid)
    have hP := untypedRetypePerformCode_eq_words src.cnode src.slot dst.cnode
      (SeLe4n.Slot.ofNat (dst.slot.toNat + i)) (retypeChildId childId i) k n dom core
      (CarveRequest.asidAtW st k asid) st
    rw [CarveRequest.ofWords_asidAtW] at hA hP
    simp only [retypeChildSlot, retypeChildId] at hA hP ⊢
    have hW := untypedRetypePerformAt_eq_words src (retypeChildSlot dst i) (retypeChildId childId i)
      ((CarveRequest.ofWords k n dom core asid).atState st) st
    simp only [retypeChildSlot, retypeChildId] at hW
    rw [hA, hP, ← hW]
    split
    · exact untypedRetypeWindowCode_eq_ofWords src dst childId k n dom core asid (i + 1) c _
    · rfl

/-- **The compiled carves are the window's**, at a request's own words. -/
theorem untypedRetypeWindowCode_eq (src dst : CSpaceAddr) (childId : SeLe4n.ObjId)
    (dom0 : SeLe4n.DomainId) (core0 : SeLe4n.Kernel.Concurrency.CoreId) (asid0 : SeLe4n.ASID)
    (req : CarveRequest) (i c : Nat) (st : SystemState) :
    untypedRetypeWindowCode src.cnode src.slot dst.cnode dst.slot childId req.kindWord req.sizeWord
        (req.domainWord dom0) (req.coreWord core0) (req.asidWord asid0) i c st =
      untypedRetypeWindowWrites src dst childId req i c st := by
  rw [untypedRetypeWindowCode_eq_ofWords, CarveRequest.ofWords_words]

/-- **The compiled refusal is the window's**, at a request's own words. -/
theorem untypedRetypeWindowRefusalCode_eq_req (st : SystemState) (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (dom0 : SeLe4n.DomainId) (core0 : SeLe4n.Kernel.Concurrency.CoreId)
    (asid0 : SeLe4n.ASID) (req : CarveRequest) (count : Nat) :
    untypedRetypeWindowRefusalCode st src dst childId req.kindWord req.sizeWord count =
      untypedRetypeWindowRefusal st src dst childId req count := by
  rw [untypedRetypeWindowRefusalCode_eq st src dst childId _ _ count (req.domainWord dom0)
    (req.coreWord core0) (req.asidWord asid0), CarveRequest.ofWords_words]
