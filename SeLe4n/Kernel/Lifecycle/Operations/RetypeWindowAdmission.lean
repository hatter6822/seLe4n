-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.RetypeWindow
import SeLe4n.Kernel.Lifecycle.Operations.SetSpace

/-!
# An admitted retype window admits every carve

WS-SX SX6.3 (D9): `untypedRetypeWindowRefusal` reads every check of a window
from the state the call is handed; each carve of `untypedRetypeWindowWrites`
reads its own admission (`untypedRetypeAdmittedAt`) at the state the carves
before it left.  `untypedRetypeWindow_admitsEveryCarve` shows the second never
refuses once the first admits: every carve of an admitted window is made, so the
writes are the window's `count` carves (`untypedRetypeWindowCarves`).

The proof carries, from carve to carve, what each carve's admission reads
(`RetypeWindowFrame`): the invoked capability (same target and rights, its free
index advanced past the carves made), the untyped (same region, its child list
grown by the carved ids), the window's slots still to fill (empty and
addressable), the ids still to take (held by no object), the object and ASID
tables' sizes (one more entry per carve) and capacities (never smaller), the
machine's bounds, and, for VSpace roots, the free ASIDs still to take.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- The window's carves, unguarded
-- ============================================================================

/-- **The window's carves** `i, i + 1, …` (`k` of them), each made without
asking its admission: what `untypedRetypeWindowWrites` writes once the window
is admitted (`untypedRetypeWindow_admitsEveryCarve`). -/
def untypedRetypeWindowCarves (src dst : CSpaceAddr) (childId : SeLe4n.ObjId)
    (req : CarveRequest) : Nat → Nat → SystemState → SystemState
  | _, 0, st => st
  | i, k + 1, st =>
    untypedRetypeWindowCarves src dst childId req (i + 1) k
      (untypedRetypePerformAt src (retypeChildSlot dst i) (retypeChildId childId i)
        (req.atState st) st)

-- ============================================================================
-- What an admitted window's checks say
-- ============================================================================

theorem retypeWindowSlotsRefusal_none {st : SystemState} {dst : CSpaceAddr} :
    ∀ {i k : Nat}, retypeWindowSlotsRefusal st dst.cnode dst.slot i k = none →
      ∀ m, m < k → cspaceDstAdmitted (retypeChildSlot dst (i + m)) st = true
  | _, 0, _, m, hm => absurd hm (Nat.not_lt_zero m)
  | i, k + 1, h, m, hm => by
    rw [retypeWindowSlotsRefusal_eq] at h
    cases hD : cspaceDstRefusal (retypeChildSlot dst i) st with
    | error e => rw [hD] at h; cases h
    | ok u =>
      rw [hD] at h
      cases m with
      | zero => exact (cspaceDstRefusal_eq_ok_iff _ st).mp hD
      | succ m =>
        have := retypeWindowSlotsRefusal_none h m (by omega)
        rwa [show i + 1 + m = i + (m + 1) by omega] at this

theorem retypeWindowIdsRefusal_none {st : SystemState} {untypedId childId : SeLe4n.ObjId}
    {ut : UntypedObject} :
    ∀ {i k : Nat}, retypeWindowIdsRefusal st untypedId childId ut i k = none →
      ∀ m, m < k →
        retypeChildId childId (i + m) ≠ untypedId ∧
        st.objects[retypeChildId childId (i + m)]? = none ∧
        isIrqNodeObjId InterruptLineSet.capacity (retypeChildId childId (i + m)) = false ∧
        childrenNameNone (retypeChildId childId (i + m)) ut.children = true ∧
        objectIdInAddressSpace st.machine (retypeChildId childId (i + m)) = true
  | _, 0, _, m, hm => absurd hm (Nat.not_lt_zero m)
  | i, k + 1, h, m, hm => by
    unfold retypeWindowIdsRefusal at h
    split at h
    · cases h
    · next hSelf =>
      split at h
      · cases h
      · next hCol =>
        split at h
        · cases h
        · next hAddr =>
          cases m with
          | zero =>
            simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hCol
            obtain ⟨⟨hObj, hIrq⟩, hKids⟩ := hCol
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hAddr
            refine ⟨hSelf, ?_, by simpa using hIrq, by simpa using hKids, by simpa using hAddr⟩
            unfold SystemState.getObject? at hObj
            simpa using hObj
          | succ m =>
            have := retypeWindowIdsRefusal_none h m (by omega)
            rwa [show i + 1 + m = i + (m + 1) by omega] at this

-- ============================================================================
-- What a carve's writes keep of the tables and the machine's bounds
-- ============================================================================

/-- **`s'` holds the object table well formed, at most `n` more objects than
`s`, and neither table smaller; the machine's heap, address width and ASID
bound are `s`'s.**  Each write of a carve keeps it with `n` its new objects. -/
structure RetypeTablesGrow (s s' : SystemState) (n : Nat) : Prop where
  objInv : s'.objects.invExt
  objSize : s'.objects.size ≤ s.objects.size + n
  objCap : s.objects.capacity ≤ s'.objects.capacity
  asidCap : s.asidTable.capacity ≤ s'.asidTable.capacity
  heap : s'.machine.kernelHeapFreeBytes = s.machine.kernelHeapFreeBytes
  width : s'.machine.physicalAddressWidth = s.machine.physicalAddressWidth
  maxAsid : s'.machine.maxASID = s.machine.maxASID

theorem RetypeTablesGrow.trans {s1 s2 s3 : SystemState} {a b : Nat}
    (h1 : RetypeTablesGrow s1 s2 a) (h2 : RetypeTablesGrow s2 s3 b) :
    RetypeTablesGrow s1 s3 (a + b) :=
  ⟨h2.objInv, by have := h1.objSize; have := h2.objSize; omega,
    Nat.le_trans h1.objCap h2.objCap, Nat.le_trans h1.asidCap h2.asidCap,
    h2.heap.trans h1.heap, h2.width.trans h1.width, h2.maxAsid.trans h1.maxAsid⟩

theorem RetypeTablesGrow.mono {s s' : SystemState} {a b : Nat} (h : RetypeTablesGrow s s' a)
    (hab : a ≤ b) : RetypeTablesGrow s s' b :=
  { h with objSize := Nat.le_trans h.objSize (by omega) }

theorem RetypeTablesGrow.of_objects_eq {s s' : SystemState} (hInv : s.objects.invExt)
    (hO : s'.objects = s.objects) (hA : s'.asidTable = s.asidTable) (hM : s'.machine = s.machine)
    (n : Nat) : RetypeTablesGrow s s' n :=
  ⟨hO ▸ hInv, by rw [hO]; omega, by rw [hO]; exact Nat.le_refl _, by rw [hA]; exact Nat.le_refl _,
    by rw [hM], by rw [hM], by rw [hM]⟩

/-- A store over a key the table holds. -/
theorem storedState_tablesGrow_present {s : SystemState} {id : SeLe4n.ObjId} {obj old : KernelObject}
    (hInv : s.objects.invExt) (hOld : s.objects[id]? = some old) :
    RetypeTablesGrow s (storedState id obj s) 0 := by
  have hS := storeObject_eq_storedState id obj s
  have hC := storeObject_capacity_le hS
  exact ⟨storeObject_preserves_objects_invExt _ _ _ _ hInv hS,
    Nat.le_trans (storeObject_size_le_of_some hS hInv hOld) (by omega), hC.1, hC.2,
    by rw [storeObject_machine_eq _ _ _ _ hS], by rw [storeObject_machine_eq _ _ _ _ hS],
    by rw [storeObject_machine_eq _ _ _ _ hS]⟩

/-- A store at any key. -/
theorem storedState_tablesGrow {s : SystemState} {id : SeLe4n.ObjId} {obj : KernelObject}
    (hInv : s.objects.invExt) : RetypeTablesGrow s (storedState id obj s) 1 := by
  have hS := storeObject_eq_storedState id obj s
  have hC := storeObject_capacity_le hS
  exact ⟨storeObject_preserves_objects_invExt _ _ _ _ hInv hS,
    storeObject_objects_size_le _ _ _ _ hInv hS, hC.1, hC.2,
    by rw [storeObject_machine_eq _ _ _ _ hS], by rw [storeObject_machine_eq _ _ _ _ hS],
    by rw [storeObject_machine_eq _ _ _ _ hS]⟩

/-- A CNode written in its slot. -/
theorem storeCNodeWith_tablesGrow {s : SystemState} (hInv : s.objects.invExt) (id : SeLe4n.ObjId)
    (f : CNode → CNode) : RetypeTablesGrow s (s.storeCNodeWith id f) 0 := by
  rcases SystemState.storeCNodeWith_cases s id f with ⟨cn, hO, hS⟩ | e
  · have hEq : s.storeCNodeWith id f = storedState id (.cnode (f cn)) s := by
      have h2 := (storeObject_eq_storedState id (.cnode (f cn)) s).symm.trans hS
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h2
      exact h2.symm
    rw [hEq]; exact storedState_tablesGrow_present hInv hO
  · rw [e]; exact RetypeTablesGrow.of_objects_eq hInv rfl rfl rfl 0

/-- A link write. -/
theorem setSlotLinkWords_tablesGrow {s : SystemState} (hInv : s.objects.invExt) (o : SeLe4n.ObjId)
    (sl : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    RetypeTablesGrow s (s.setSlotLinkWords o sl f c w) 0 := by
  cases hob : s.objects[o]? with
  | none =>
    rw [SystemState.setSlotLinkWords_of_not_slots (fun ob h => by rw [hob] at h; cases h)]
    exact RetypeTablesGrow.of_objects_eq hInv rfl rfl rfl 0
  | some ob =>
    rcases SystemState.setSlotLinkWords_of_object hob sl f c w with e | ⟨_, e⟩
    · rw [e]
      exact ⟨RHTable_insert_preserves_invExt _ _ _ hInv,
        Nat.le_trans (RobinHood.RHTable.size_insert_le_of_get? s.objects o _ ob hInv
          (by rw [← RHTable_getElem?_eq_get?]; exact hob)) (by omega),
        RobinHood.RHTable.capacity_le_insert _ _ _, Nat.le_refl _, rfl, rfl, rfl⟩
    · rw [e]; exact RetypeTablesGrow.of_objects_eq hInv rfl rfl rfl 0

/-- A link write after writes that kept the tables. -/
theorem RetypeTablesGrow.link {s0 s : SystemState} {n : Nat} (h : RetypeTablesGrow s0 s n)
    (o : SeLe4n.ObjId) (sl : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    RetypeTablesGrow s0 (s.setSlotLinkWords o sl f c w) n :=
  (h.trans (setSlotLinkWords_tablesGrow h.objInv o sl f c w)).mono (by omega)

/-- A derivation edge and its links. -/
theorem cdtAddChild_tablesGrow {s : SystemState} (hInv : s.objects.invExt) (p c : SlotRef)
    (op : DerivationOp) : RetypeTablesGrow s (s.cdtAddChild p c op) 0 := by
  have h0 : RetypeTablesGrow s (s.modifyCdt (·.addEdge p c op)) 0 :=
    RetypeTablesGrow.of_objects_eq (s' := s.modifyCdt (·.addEdge p c op)) hInv rfl rfl rfl 0
  unfold SystemState.cdtAddChild SystemState.linkAddChild
  dsimp only
  split
  · exact (((h0.link _ _ _ _ _).link _ _ _ _ _).link _ _ _ _ _).link _ _ _ _ _
  · exact ((((h0.link _ _ _ _ _).link _ _ _ _ _).link _ _ _ _ _).link _ _ _ _ _).link _ _ _ _ _

/-- The scrub writes memory, not the machine's address width. -/
theorem CarveRequest.scrub_physicalAddressWidth (st : SystemState) (ut : UntypedObject) (idx : Nat)
    (req : CarveRequest) :
    (req.scrub st ut idx).machine.physicalAddressWidth = st.machine.physicalAddressWidth := by
  cases req <;> simp only [CarveRequest.scrub, carveZeroFrame] <;> (try split) <;> rfl

/-- The scrub writes no ASID. -/
theorem CarveRequest.scrub_asidTable (st : SystemState) (ut : UntypedObject) (idx : Nat)
    (req : CarveRequest) : (req.scrub st ut idx).asidTable = st.asidTable := by
  cases req <;> simp only [CarveRequest.scrub, carveZeroFrame] <;> (try split) <;> rfl

/-- The scrub moves no object, writes no ASID and changes no machine bound. -/
theorem CarveRequest.scrub_tablesGrow {s : SystemState} (hInv : s.objects.invExt)
    (req : CarveRequest) (ut : UntypedObject) (idx : Nat) :
    RetypeTablesGrow s (req.scrub s ut idx) 0 := by
  refine ⟨by rw [CarveRequest.scrub_objects]; exact hInv, by rw [CarveRequest.scrub_objects]; omega,
    by rw [CarveRequest.scrub_objects]; exact Nat.le_refl _,
    by rw [CarveRequest.scrub_asidTable]; exact Nat.le_refl _, ?_,
    CarveRequest.scrub_physicalAddressWidth s ut idx req, ?_⟩ <;>
  cases req <;> simp only [CarveRequest.scrub, carveZeroFrame] <;> (try split) <;> rfl

-- ============================================================================
-- What a carve's writes do to the objects a window reads
-- ============================================================================

theorem storedState_objects {s : SystemState} (hInv : s.objects.invExt) (id : SeLe4n.ObjId)
    (obj : KernelObject) (x : SeLe4n.ObjId) :
    (storedState id obj s).objects[x]? = if x = id then some obj else s.objects[x]? := by
  have hS := storeObject_eq_storedState id obj s
  split
  · next h => subst h; exact storeObject_objects_eq _ _ _ _ hInv hS
  · next h => exact storeObject_objects_ne _ _ _ _ _ h hInv hS

theorem storeCNodeWith_objects_at {s : SystemState} (hInv : s.objects.invExt) {id : SeLe4n.ObjId}
    {cn : CNode} (h : s.objects[id]? = some (.cnode cn)) (f : CNode → CNode) (x : SeLe4n.ObjId) :
    (s.storeCNodeWith id f).objects[x]? = if x = id then some (.cnode (f cn)) else s.objects[x]? := by
  have hS := SystemState.storeObject_cnode_eq_storeCNodeWith h f
  split
  · next hx => subst hx; exact storeObject_objects_eq _ _ _ _ hInv hS
  · next hx => exact storeObject_objects_ne _ _ _ _ _ hx hInv hS

/-- A CNode written in its slot writes no ASID. -/
theorem storeCNodeWith_asidTable (s : SystemState) (id : SeLe4n.ObjId) (f : CNode → CNode) :
    (s.storeCNodeWith id f).asidTable = s.asidTable := by
  rcases SystemState.storeCNodeWith_cases s id f with ⟨cn, hO, hS⟩ | e
  · unfold storeObject at hS
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
    rw [← hS]
    simp [storeKeepsAsid, hO]
  · rw [e]

/-- A store over an object that is no VSpace root, of one that is none, writes
no ASID. -/
theorem storedState_asidTable_of_nonRoot {s : SystemState} {id : SeLe4n.ObjId}
    {obj old : KernelObject} (hOld : s.objects[id]? = some old)
    (hO : ∀ r, old ≠ .vspaceRoot r) (hN : ∀ r, obj ≠ .vspaceRoot r) :
    (storedState id obj s).asidTable = s.asidTable := by
  have hS := storeObject_eq_storedState id obj s
  unfold storeObject at hS
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
  rw [← hS]
  dsimp only
  have hK : storeKeepsAsid s id obj = false := by
    unfold storeKeepsAsid; cases obj <;> try rfl
    next r => exact absurd rfl (hN r)
  rw [if_neg (by rw [hK]; decide), hOld]
  cases old <;> (try (next r => exact absurd rfl (hO r))) <;>
    (cases obj <;> (try (next r => exact absurd rfl (hN r))) <;> rfl)

/-- A store at an id no object holds: a VSpace root inserts its ASID. -/
theorem storedState_asidTable_fresh {s : SystemState} {id : SeLe4n.ObjId} {obj : KernelObject}
    (hNone : s.objects[id]? = none) :
    (storedState id obj s).asidTable =
      match obj with
      | .vspaceRoot r => s.asidTable.insert r.asid id
      | _ => s.asidTable := by
  have hS := storeObject_eq_storedState id obj s
  unfold storeObject at hS
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
  rw [← hS]
  dsimp only
  have hK : storeKeepsAsid s id obj = false := by
    unfold storeKeepsAsid; cases obj <;> simp [hNone]
  rw [if_neg (by rw [hK]; decide), hNone]
  cases obj <;> rfl

/-- Objects that agree off their links: one that holds no slot is the same
object. -/
theorem agreeAt_eq_of_noSlots {s s' : SystemState} {x : SeLe4n.ObjId} {o : KernelObject}
    (h : SystemState.objectAgreesOffDerivationLinksAt s' s x) (hx : s.objects[x]? = some o)
    (hC : ∀ cn, o ≠ .cnode cn) (hT : ∀ t, o ≠ .tcb t) : s'.objects[x]? = some o := by
  rcases h with e | ⟨cn, _, ha, _, _⟩ | ⟨t, _, ha, _, _⟩
  · rw [e, hx]
  · rw [hx] at ha; cases ha; exact absurd rfl (hC cn)
  · rw [hx] at ha; cases ha; exact absurd rfl (hT t)

/-- Objects that agree off their links: no object stays no object. -/
theorem agreeAt_none {s s' : SystemState} {x : SeLe4n.ObjId}
    (h : SystemState.objectAgreesOffDerivationLinksAt s' s x) (hx : s.objects[x]? = none) :
    s'.objects[x]? = none := by
  rcases h with e | ⟨_, _, ha, _, _⟩ | ⟨_, _, ha, _, _⟩
  · rw [e, hx]
  · rw [hx] at ha; cases ha
  · rw [hx] at ha; cases ha

/-- Objects that agree off their links: a CNode is a CNode with the same slots
and radix. -/
theorem agreeAt_cnode {s s' : SystemState} {x : SeLe4n.ObjId} {cn : CNode}
    (h : SystemState.objectAgreesOffDerivationLinksAt s' s x) (hx : s.objects[x]? = some (.cnode cn)) :
    ∃ cn', s'.objects[x]? = some (.cnode cn') ∧ cn'.radixWidth = cn.radixWidth ∧
      ∀ sl, cn'.lookup sl = cn.lookup sl := by
  rcases h with e | ⟨cn0, cn', ha, hb, hw⟩ | ⟨_, _, ha, _, _⟩
  · exact ⟨cn, by rw [e, hx], rfl, fun _ => rfl⟩
  · rw [hx] at ha; cases ha
    exact ⟨cn', hb, CNode.proj_eq_of_withoutLinks_eq (·.radixWidth) hw,
      fun sl => CNode.proj_eq_of_withoutLinks_eq (·.lookup sl) hw⟩
  · rw [hx] at ha; cases ha

/-- **A derivation edge leaves its parent with a child.** -/
theorem hasCdtChildren_cdtAddChild {s : SystemState} (hInv : s.objects.invExt) {p : SlotRef}
    (hp : s.slotInObject p) (c : SlotRef) (op : DerivationOp) :
    hasCdtChildren (s.cdtAddChild p c op) p = true := by
  unfold hasCdtChildren SystemState.linkHasChild SystemState.cdtAddChild SystemState.linkAddChild
  dsimp only
  have h0 : (s.modifyCdt (·.addEdge p c op)).objects.invExt := hInv
  have hParentIn : (s.modifyCdt (·.addEdge p c op)).slotInObject p := hp
  generalize s.modifyCdt (·.addEdge p c op) = s0 at h0 hParentIn
  have key : ∀ (t : SystemState), t.objects.invExt → t.slotInObject p →
      ((t.setSlotLinkWords p.cnode p.slot .firstChild (c.cnode.toNat + 1) (c.slot.toNat + 1)
        ).slotLinkNodeWord p.cnode p.slot .firstChild != 0) = true := by
    intro t ht hpt
    have hL := SystemState.slotLinkAt_setSlotLinkWords_ref ht hpt .firstChild
      (c.cnode.toNat + 1) (c.slot.toNat + 1)
    have hA := congrFun (congrFun hL p) .firstChild
    rw [SystemState.slotLinkAt_eq_decode] at hA
    simp only [LinkView.set_same] at hA
    cases hz : (t.setSlotLinkWords p.cnode p.slot .firstChild (c.cnode.toNat + 1)
      (c.slot.toNat + 1)).slotLinkNodeWord p.cnode p.slot .firstChild with
    | zero => rw [hz] at hA; simp [decodeLink] at hA
    | succ _ => rfl
  have step : ∀ (t : SystemState) o sl f a b, t.objects.invExt → t.slotInObject p →
      (t.setSlotLinkWords o sl f a b).objects.invExt ∧ (t.setSlotLinkWords o sl f a b).slotInObject p :=
    fun t o sl f a b ht hpt => ⟨SystemState.setSlotLinkWords_invExt ht o sl f a b,
      (SystemState.slotInObject_setSlotLinkWords ht o sl f a b p).mpr hpt⟩
  have q1 := step _ c.cnode c.slot .parent (p.cnode.toNat + 1) (p.slot.toNat + 1) h0 hParentIn
  have q2 := step _ c.cnode c.slot .next (s0.slotLinkNodeWord p.cnode p.slot .firstChild)
    (s0.slotLinkSlotWord p.cnode p.slot .firstChild) q1.1 q1.2
  have q3 := step _ c.cnode c.slot .prev 0 0 q2.1 q2.2
  split
  · exact key _ q3.1 q3.2
  · apply key
    · exact (step _ _ _ _ _ _ q3.1 q3.2).1
    · exact (step _ _ _ _ _ _ q3.1 q3.2).2

/-- An occupied slot is a slot of a CNode the store holds. -/
theorem lookupSlotCap_some {s : SystemState} {r : SlotRef} {cap : Capability}
    (h : SystemState.lookupSlotCap s r = some cap) :
    ∃ cn, s.objects[r.cnode]? = some (.cnode cn) ∧ cn.lookup r.slot = some cap := by
  unfold SystemState.lookupSlotCap SystemState.lookupCNode at h
  revert h
  cases hO : s.objects[r.cnode]? with
  | none => simp
  | some o =>
    cases o
    case cnode cn => exact fun h => ⟨cn, rfl, h⟩
    all_goals simp

/-- **A carve's writes, step by step**: the untyped's record, the new object,
the invoked capability's free index, the scrub, the destination's capability
and the derivation edge. -/
theorem untypedRetypePerformAt_eq {src dst : CSpaceAddr} {childId U : SeLe4n.ObjId}
    {req : CarveRequest} {s : SystemState} {cap : Capability} {ut : UntypedObject}
    (hL : SystemState.lookupSlotCap s src = some cap) (hT : cap.target = .object U)
    (hU : s.getUntyped? U = some ut) :
    untypedRetypePerformAt src dst childId req s =
      ((req.scrub
        ((storedState childId (req.object U childId ut (req.carveIndex ut (retypeFreeIndex s src cap)))
          (storedState U (.untyped (ut.allocated (req.carveIndex ut (retypeFreeIndex s src cap))
            childId req.size)) s)).storeCNodeWith src.cnode
          (·.setFreeIndex src.slot (req.carveIndex ut (retypeFreeIndex s src cap) + req.size)))
        ut (req.carveIndex ut (retypeFreeIndex s src cap))).storeCNodeWith dst.cnode
          (·.insert dst.slot (req.capability childId))).cdtAddChild src dst .retype := by
  unfold untypedRetypePerformAt
  simp only [hL, hT, hU]
  rfl

/-- **What one carve of a window does to what the next carve reads.**  Over a
store whose object table is well formed, a carve through the untyped
capability `cap` in `src` (naming the untyped `ut` at `U`) into the empty slot
`dst` at the free id `childId`: grows the tables by one object; advances the
capability's free index past the carved object; leaves `src` with a derivation
child; records the child in the untyped; keeps every other empty slot of
`dst`'s CNode empty and addressable; keeps every other free id free; and
writes the ASID table only for a VSpace root, at its ASID. -/
theorem untypedRetypePerformAt_frame {src dst : CSpaceAddr} {childId U : SeLe4n.ObjId}
    {req : CarveRequest} {s : SystemState} {cap : Capability} {ut : UntypedObject}
    (hInv : s.objects.invExt)
    (hL : SystemState.lookupSlotCap s src = some cap) (hT : cap.target = .object U)
    (hU : s.getUntyped? U = some ut) (hD : cspaceDstAdmitted dst s = true)
    (hFresh : s.objects[childId]? = none) :
    RetypeTablesGrow s (untypedRetypePerformAt src dst childId req s) 1 ∧
    SystemState.lookupSlotCap (untypedRetypePerformAt src dst childId req s) src =
      some (cap.withFreeIndex (req.carveIndex ut (retypeFreeIndex s src cap) + req.size)) ∧
    hasCdtChildren (untypedRetypePerformAt src dst childId req s) src = true ∧
    (untypedRetypePerformAt src dst childId req s).getUntyped? U =
      some (ut.allocated (req.carveIndex ut (retypeFreeIndex s src cap)) childId req.size) ∧
    (∀ r : CSpaceAddr, r.cnode = dst.cnode → r.slot ≠ dst.slot →
      cspaceDstAdmitted r s = true →
        cspaceDstAdmitted r (untypedRetypePerformAt src dst childId req s) = true) ∧
    (∀ x, x ≠ childId → s.objects[x]? = none →
      (untypedRetypePerformAt src dst childId req s).objects[x]? = none) ∧
    (untypedRetypePerformAt src dst childId req s).asidTable =
      (match req with
       | .vspaceRoot a => s.asidTable.insert a childId
       | _ => s.asidTable) := by
  rw [untypedRetypePerformAt_eq hL hT hU]
  -- The keys the carve writes, and what each held.
  have hObjU : s.objects[U]? = some (.untyped ut) := (SystemState.getUntyped?_eq_some_iff s U ut).mp hU
  obtain ⟨cnS, hObjS, hLkS⟩ := lookupSlotCap_some hL
  obtain ⟨cnD, hObjD, hAddrD, hEmptyD⟩ : ∃ cnD, s.objects[dst.cnode]? = some (.cnode cnD) ∧
      cnD.slotAddressable dst.slot = true ∧ cnD.lookup dst.slot = none := by
    unfold cspaceDstAdmitted at hD
    cases hC : s.getCNode? dst.cnode with
    | none => rw [hC] at hD; cases hD
    | some cn =>
      rw [hC] at hD
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hD
      exact ⟨cn, (SystemState.getCNode?_eq_some_iff s _ cn).mp hC, hD.1, hD.2⟩
  have hUS : U ≠ src.cnode := by intro h; rw [h, hObjS] at hObjU; cases hObjU
  have hUD : U ≠ dst.cnode := by intro h; rw [h, hObjD] at hObjU; cases hObjU
  have hCU : childId ≠ U := by intro h; rw [h, hObjU] at hFresh; cases hFresh
  have hCS : childId ≠ src.cnode := by intro h; rw [h, hObjS] at hFresh; cases hFresh
  have hCD : childId ≠ dst.cnode := by intro h; rw [h, hObjD] at hFresh; cases hFresh
  have hSlotNe : dst.cnode = src.cnode → dst.slot ≠ src.slot := by
    intro hc hs; rw [hc, hObjS] at hObjD; cases hObjD; rw [hs, hLkS] at hEmptyD; cases hEmptyD
  -- The states.
  generalize hIdx : req.carveIndex ut (retypeFreeIndex s src cap) = idx
  generalize hObj : req.object U childId ut idx = obj
  generalize hA : storedState U (.untyped (ut.allocated idx childId req.size)) s = sA
  generalize hB : storedState childId obj sA = sB
  generalize hC : sB.storeCNodeWith src.cnode (·.setFreeIndex src.slot (idx + req.size)) = sC
  generalize hDd : req.scrub sC ut idx = sD
  generalize hE : sD.storeCNodeWith dst.cnode (·.insert dst.slot (req.capability childId)) = sE
  have gA : RetypeTablesGrow s sA 0 := hA ▸ storedState_tablesGrow_present hInv hObjU
  have oA : ∀ x, sA.objects[x]? = if x = U then some (.untyped (ut.allocated idx childId req.size))
      else s.objects[x]? := fun x => hA ▸ storedState_objects hInv _ _ x
  have gB : RetypeTablesGrow sA sB 1 := hB ▸ storedState_tablesGrow gA.objInv
  have oB : ∀ x, sB.objects[x]? = if x = childId then some obj else sA.objects[x]? :=
    fun x => hB ▸ storedState_objects gA.objInv _ _ x
  have hBS : sB.objects[src.cnode]? = some (.cnode cnS) := by
    rw [oB, if_neg (Ne.symm hCS), oA, if_neg (Ne.symm hUS)]; exact hObjS
  have gC : RetypeTablesGrow sB sC 0 := hC ▸ storeCNodeWith_tablesGrow gB.objInv _ _
  have oC : ∀ x, sC.objects[x]? = if x = src.cnode then
      some (.cnode (cnS.setFreeIndex src.slot (idx + req.size))) else sB.objects[x]? :=
    fun x => hC ▸ storeCNodeWith_objects_at gB.objInv hBS _ x
  have gD : RetypeTablesGrow sC sD 0 := hDd ▸ CarveRequest.scrub_tablesGrow gC.objInv req ut idx
  have oD : sD.objects = sC.objects := by rw [← hDd, CarveRequest.scrub_objects]
  -- The destination's CNode before its write.
  obtain ⟨cnD', hDD, hRadD, hLkD', hLkDS⟩ : ∃ cnD', sD.objects[dst.cnode]? = some (.cnode cnD') ∧
      cnD'.radixWidth = cnD.radixWidth ∧
      (∀ sl, (dst.cnode = src.cnode → sl ≠ src.slot) → cnD'.lookup sl = cnD.lookup sl) ∧
      (dst.cnode = src.cnode → cnD'.lookup src.slot = some (cap.withFreeIndex (idx + req.size))) := by
    rw [oD, oC]
    by_cases hc : dst.cnode = src.cnode
    · rw [if_pos hc]
      have hcn : cnD = cnS := by rw [hc, hObjS] at hObjD; cases hObjD; rfl
      subst hcn
      refine ⟨_, rfl, CNode.setFreeIndex_radixWidth _ _ _, fun sl hsl => ?_, fun _ => ?_⟩
      · exact CNode.lookup_setFreeIndex_ne _ _ (Ne.symm (hsl hc))
      · rw [CNode.lookup_setFreeIndex_self, hLkS]; rfl
    · rw [if_neg hc, oB, if_neg (Ne.symm hCD), oA, if_neg (Ne.symm hUD)]
      exact ⟨cnD, hObjD, rfl, fun _ _ => rfl, fun h => absurd h hc⟩
  have gE : RetypeTablesGrow sD sE 0 := hE ▸ storeCNodeWith_tablesGrow gD.objInv _ _
  have oE : ∀ x, sE.objects[x]? = if x = dst.cnode then
      some (.cnode (cnD'.insert dst.slot (req.capability childId))) else sD.objects[x]? :=
    fun x => hE ▸ storeCNodeWith_objects_at gD.objInv hDD _ x
  have gF := cdtAddChild_tablesGrow gE.objInv src dst .retype
  have hAg := (SystemState.cdtAddChild_agreeObjects gE.objInv src dst .retype).1
  -- The invoked capability's slot after the destination's write.
  have hES : SystemState.lookupSlotCap sE src = some (cap.withFreeIndex (idx + req.size)) := by
    unfold SystemState.lookupSlotCap SystemState.lookupCNode
    by_cases hc : src.cnode = dst.cnode
    · rw [oE, if_pos hc]
      dsimp only
      rw [CNode.lookup_insert_ne _ _ _ _ (hSlotNe hc.symm) (CNode.slotsUnique_holds _)]
      exact hLkDS hc.symm
    · rw [oE, if_neg hc, oD, oC, if_pos rfl]
      dsimp only
      rw [CNode.lookup_setFreeIndex_self, hLkS]; rfl
  refine ⟨((((gA.trans gB).trans gC).trans gD).trans gE).trans gF |>.mono (by omega), ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [lookupSlotCap_of_agreeAt (hAg src.cnode)]; exact hES
  · apply hasCdtChildren_cdtAddChild gE.objInv
    obtain ⟨cn, h, hLk⟩ := lookupSlotCap_some hES
    refine ⟨_, h, ?_⟩
    have := CNode.slotAddressable_of_lookup _ _ _ hLk
    simpa [CNode.slotAddressable, CNode.slotCount, KernelObject.hasSlot] using this
  · rw [SystemState.getUntyped?_eq_some_iff]
    apply agreeAt_eq_of_noSlots (hAg U) _ (fun _ h => by cases h) (fun _ h => by cases h)
    rw [oE, if_neg hUD, oD, oC, if_neg hUS, oB, if_neg (Ne.symm hCU), oA, if_pos rfl]
  · intro r hr hrs hrA
    obtain ⟨cnR, hObjR, hAddrR, hEmptyR⟩ : ∃ cnR, s.objects[r.cnode]? = some (.cnode cnR) ∧
        cnR.slotAddressable r.slot = true ∧ cnR.lookup r.slot = none := by
      unfold cspaceDstAdmitted at hrA
      cases hCr : s.getCNode? r.cnode with
      | none => rw [hCr] at hrA; cases hrA
      | some cn =>
        rw [hCr] at hrA
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hrA
        exact ⟨cn, (SystemState.getCNode?_eq_some_iff s _ cn).mp hCr, hrA.1, hrA.2⟩
    have hcn : cnR = cnD := by rw [hr, hObjD] at hObjR; cases hObjR; rfl
    subst hcn
    have hEr : sE.objects[r.cnode]? = some (.cnode (cnD'.insert dst.slot (req.capability childId))) := by
      rw [oE, if_pos hr]
    obtain ⟨cn'', hObj'', hRad'', hLk''⟩ := agreeAt_cnode (hAg r.cnode) hEr
    unfold cspaceDstAdmitted
    rw [(SystemState.getCNode?_eq_some_iff _ _ cn'').mpr hObj'']
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none]
    refine ⟨?_, ?_⟩
    · unfold CNode.slotAddressable CNode.slotCount at hAddrR ⊢
      rw [hRad'', CNode.insert_radixWidth, hRadD]; exact hAddrR
    · rw [hLk'', CNode.lookup_insert_ne _ _ _ _ (Ne.symm hrs) (CNode.slotsUnique_holds _)]
      rw [hLkD' r.slot (fun hc hs => by
        have hk : r.cnode = src.cnode := hr.trans hc
        rw [hk, hObjS] at hObjR; cases hObjR
        rw [hs, hLkS] at hEmptyR; cases hEmptyR)]
      exact hEmptyR
  · intro x hx hxN
    have hxU : x ≠ U := by intro h; rw [h, hObjU] at hxN; cases hxN
    have hxS : x ≠ src.cnode := by intro h; rw [h, hObjS] at hxN; cases hxN
    have hxD : x ≠ dst.cnode := by intro h; rw [h, hObjD] at hxN; cases hxN
    apply agreeAt_none (hAg x)
    rw [oE, if_neg hxD, oD, oC, if_neg hxS, oB, if_neg hx, oA, if_neg hxU]; exact hxN
  · rw [SystemState.cdtAddChild_asidTable, ← hE, storeCNodeWith_asidTable, ← hDd,
      CarveRequest.scrub_asidTable, ← hC, storeCNodeWith_asidTable, ← hB,
      storedState_asidTable_fresh (by rw [oA, if_neg hCU]; exact hFresh), ← hA,
      storedState_asidTable_of_nonRoot hObjU (fun _ h => by cases h) (fun _ h => by cases h), ← hObj]
    cases req <;> rfl

-- ============================================================================
-- The ASIDs a window's roots take
-- ============================================================================

theorem freshAsidsFrom_zero (st : SystemState) (fuel n : Nat) : freshAsidsFrom st fuel n 0 = true := by
  cases fuel <;> simp [freshAsidsFrom]

theorem freshAsidsFrom_some (st : SystemState) :
    ∀ (fuel n k : Nat), freshAsidsFrom st fuel n (k + 1) = true →
      ∃ a, freshAsidFrom st fuel n = some a
  | 0, _, _, h => by simp [freshAsidsFrom] at h
  | fuel + 1, n, k, h => by
    unfold freshAsidsFrom at h; unfold freshAsidFrom
    split at h
    · next hLt =>
      rw [if_pos hLt]
      split at h
      · next hF => rw [if_pos hF]; exact ⟨_, rfl⟩
      · next hF => rw [if_neg hF]; exact freshAsidsFrom_some st fuel (n + 1) k h
    · cases h

theorem freshAsidsFrom_pred (st : SystemState) :
    ∀ (fuel n k : Nat), freshAsidsFrom st fuel n (k + 1) = true → freshAsidsFrom st fuel n k = true
  | fuel, n, 0, _ => freshAsidsFrom_zero st fuel n
  | 0, _, _ + 1, h => by simp [freshAsidsFrom] at h
  | fuel + 1, n, k + 1, h => by
    unfold freshAsidsFrom at h ⊢
    split at h
    · next hLt =>
      rw [if_pos hLt]
      split at h
      · next hF => rw [if_pos hF]; exact freshAsidsFrom_pred st fuel (n + 1) k h
      · next hF => rw [if_neg hF]; exact freshAsidsFrom_pred st fuel (n + 1) (k + 1) h
    · cases h

/-- **Free ASIDs that stay free are still counted.** -/
theorem freshAsidsFrom_transfer {st st' : SystemState} (hMax : st'.machine.maxASID = st.machine.maxASID) :
    ∀ (fuel n k : Nat),
      (∀ m, n ≤ m → (st.asidTable[SeLe4n.ASID.ofNat m]?).isNone = true →
        (st'.asidTable[SeLe4n.ASID.ofNat m]?).isNone = true) →
      freshAsidsFrom st fuel n k = true → freshAsidsFrom st' fuel n k = true
  | fuel, n, 0, _, _ => freshAsidsFrom_zero st' fuel n
  | 0, _, _ + 1, _, h => by simp [freshAsidsFrom] at h
  | fuel + 1, n, k + 1, hF, h => by
    unfold freshAsidsFrom at h ⊢
    have hF' : ∀ m, n + 1 ≤ m → (st.asidTable[SeLe4n.ASID.ofNat m]?).isNone = true →
        (st'.asidTable[SeLe4n.ASID.ofNat m]?).isNone = true := fun m hm => hF m (by omega)
    rw [hMax]
    split at h
    · next hLt =>
      rw [if_pos hLt]
      split at h
      · next hFr =>
        rw [if_pos (hF n (Nat.le_refl n) hFr)]
        exact freshAsidsFrom_transfer hMax fuel (n + 1) k hF' h
      · next hFr =>
        split
        · exact freshAsidsFrom_pred st' fuel (n + 1) k
            (freshAsidsFrom_transfer hMax fuel (n + 1) (k + 1) hF' h)
        · exact freshAsidsFrom_transfer hMax fuel (n + 1) (k + 1) hF' h
    · cases h

/-- **A root's carve takes one of the free ASIDs a window counted**: the one the
scan answers; every other free ASID stays free, so one fewer is left. -/
theorem freshAsidsFrom_step {st st' : SystemState} {a : SeLe4n.ASID}
    (hMax : st'.machine.maxASID = st.machine.maxASID)
    (hF : ∀ m, m ≠ a.toNat → (st.asidTable[SeLe4n.ASID.ofNat m]?).isNone = true →
      (st'.asidTable[SeLe4n.ASID.ofNat m]?).isNone = true) :
    ∀ (fuel n k : Nat), freshAsidsFrom st fuel n (k + 1) = true →
      freshAsidFrom st fuel n = some a → freshAsidsFrom st' fuel n k = true
  | 0, _, _, h, _ => by simp [freshAsidsFrom] at h
  | fuel + 1, n, k, h, hA => by
    unfold freshAsidsFrom at h; unfold freshAsidFrom at hA
    split at h
    · next hLt =>
      rw [if_pos hLt] at hA
      split at h
      · next hFr =>
        rw [if_pos hFr] at hA
        cases hA
        have hT : freshAsidsFrom st' fuel (n + 1) k = true :=
          freshAsidsFrom_transfer hMax fuel (n + 1) k
            (fun m hm hm' => hF m (by simp [SeLe4n.ASID.toNat_ofNat]; omega) hm') h
        cases k with
        | zero => exact freshAsidsFrom_zero st' (fuel + 1) n
        | succ k =>
          unfold freshAsidsFrom; rw [hMax, if_pos hLt]
          split
          · exact freshAsidsFrom_pred st' fuel (n + 1) k hT
          · exact hT
      · next hFr =>
        rw [if_neg hFr] at hA
        have ih := freshAsidsFrom_step hMax hF fuel (n + 1) k h hA
        cases k with
        | zero => exact freshAsidsFrom_zero st' (fuel + 1) n
        | succ k =>
          unfold freshAsidsFrom; rw [hMax, if_pos hLt]
          split
          · exact freshAsidsFrom_pred st' fuel (n + 1) k ih
          · exact ih
    · cases h

-- ============================================================================
-- The window's objects lie one after another
-- ============================================================================

theorem alignUpNat_of_mod_eq_zero {n a : Nat} (h : n % a = 0) : alignUpNat n a = n := by
  unfold alignUpNat
  split
  · rfl
  · next ha =>
    obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
    have hpos : 0 < a := Nat.pos_of_ne_zero ha
    rw [Nat.mul_comm a q]
    have : (q * a + a - 1) / a = q := by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [Nat.succ_mul]; omega
    rw [this]

/-- Every kind's size is a multiple of its boundary. -/
theorem CarveRequest.size_mod_carveAlignment (req : CarveRequest) :
    req.size % carveAlignment req.objectType req.size = 0 := by
  cases req <;> simp [carveAlignment, requiresPageAlignment, requiresSizeAlignment,
    CarveRequest.size, CarveRequest.objectType, SeLe4n.pageBytes]

/-- A boundary is never 0 for an object of some bytes. -/
theorem carveAlignment_pos (ty : KernelObjectType) {size : Nat} (h : 0 < size) :
    0 < carveAlignment ty size := by
  unfold carveAlignment; split
  · decide
  · split <;> omega

/-- **The rounded index is on the boundary.** -/
theorem alignedCarveIndex_aligned (ty : KernelObjectType) {size : Nat} (hS : 0 < size)
    (ut : UntypedObject) (idx : Nat) :
    (ut.regionBase.toNat + alignedCarveIndex ty size ut idx) % carveAlignment ty size = 0 := by
  have hle := le_alignUpNat (ut.regionBase.toNat + idx) (carveAlignment ty size)
  have hEq : ut.regionBase.toNat + alignedCarveIndex ty size ut idx =
      alignUpNat (ut.regionBase.toNat + idx) (carveAlignment ty size) := by
    unfold alignedCarveIndex; omega
  rw [hEq]
  exact alignUpNat_mod _ _ (Nat.pos_iff_ne_zero.mp (carveAlignment_pos ty hS))

/-- **Object `j` of a window starts where the `j` before it end**: an index on
the boundary, past whole objects of a size the boundary divides, is on it. -/
theorem alignedCarveIndex_window (req : CarveRequest) (ut : UntypedObject) {a0 : Nat}
    (hA : (ut.regionBase.toNat + a0) % carveAlignment req.objectType req.size = 0) (j : Nat) :
    alignedCarveIndex req.objectType req.size ut (a0 + j * req.size) = a0 + j * req.size := by
  unfold alignedCarveIndex
  rw [alignUpNat_of_mod_eq_zero]
  · omega
  · rw [← Nat.add_assoc, Nat.add_mod, hA, Nat.mul_mod, req.size_mod_carveAlignment]; simp

-- ============================================================================
-- The heap a window's carve asks
-- ============================================================================

/-- **A window's resize bound covers each carve's**: a table that has taken at
most `j` of a window's `n` new keys, `j < n`, and is no smaller than the table
the window was checked on, resizes on its next insert into no more than the
window's bound. -/
theorem rhInsertResizeHeapBytes_le_window {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    {t : SeLe4n.Kernel.RobinHood.RHTable α β} {size capacity n j : Nat}
    (hS : t.size ≤ size + j) (hj : j < n) (hC : capacity ≤ t.capacity) :
    rhInsertResizeHeapBytes t ≤ rhWindowResizeHeapBytes size capacity n := by
  unfold rhInsertResizeHeapBytes rhWindowResizeHeapBytes rhSlotHeapBytes
  split
  · rw [if_pos (by omega)]; omega
  · exact Nat.zero_le _

theorem CarveRequest.atState_objectType (st : SystemState) (req : CarveRequest) :
    (req.atState st).objectType = req.objectType := by cases req <;> rfl

theorem CarveRequest.atState_size (st : SystemState) (req : CarveRequest) :
    (req.atState st).size = req.size := by cases req <;> rfl

/-- **Each carve of an admitted window asks the heap no more than the window
did.** -/
theorem CarveRequest.heapBytes_atState_le_window {s st : SystemState} {req : CarveRequest}
    {count : Nat} (hc : 0 < count)
    (hO : rhInsertResizeHeapBytes s.objects ≤
      rhWindowResizeHeapBytes st.objects.size st.objects.capacity count)
    (hA : rhInsertResizeHeapBytes s.asidTable ≤
      rhWindowResizeHeapBytes st.asidTable.size st.asidTable.capacity count) :
    (req.atState s).heapBytes s ≤ req.windowHeapBytes st count := by
  have hX := Nat.le_mul_of_pos_left req.objectHeapBytes hc
  have hOH : (req.atState s).objectHeapBytes = req.objectHeapBytes := by cases req <;> rfl
  unfold CarveRequest.heapBytes CarveRequest.windowHeapBytes
  rw [hOH]
  generalize req.objectHeapBytes = X at hX ⊢
  cases req <;> dsimp only [CarveRequest.atState] <;> omega

-- ============================================================================
-- From carve to carve
-- ============================================================================

/-- **What an admitted window's checks fix for all its carves**, read on the
state `st` it was handed: the ids (none the untyped's own, none an interrupt
node's, each inside the address space), the device rule, the size, the region
holding all `count` objects from the first one's index `a0` on its boundary,
the object store's capacity and the kernel heap. -/
structure RetypeWindowChecks (st : SystemState) (childId U : SeLe4n.ObjId) (req : CarveRequest)
    (count : Nat) (ut0 : UntypedObject) (a0 : Nat) : Prop where
  ids : ∀ m, m < count → retypeChildId childId m ≠ U ∧
    isIrqNodeObjId InterruptLineSet.capacity (retypeChildId childId m) = false ∧
    objectIdInAddressSpace st.machine (retypeChildId childId m) = true
  device : (ut0.isDevice && !req.objectType.deviceBackable) = false
  allocSize : ¬ req.size < objectTypeAllocSize req.objectType
  sizePos : 0 < req.size
  fits : a0 + count * req.size ≤ ut0.regionSize
  aligned : (ut0.regionBase.toNat + a0) % carveAlignment req.objectType req.size = 0
  capacity : st.objects.size + count ≤ maxObjects
  heap : req.windowHeapBytes st count ≤ st.machine.kernelHeapFreeBytes

/-- **What carve `j` of a window reads, at the state `s` the `j` carves before
it left**: the invoked capability `cap` (the untyped's target and retype
right, its index past the `j` objects), the untyped `ut` (the region it was,
its children no window id still to take), every slot and id still to take
empty and free, the tables grown by at most `j` objects and no smaller, and,
for VSpace roots, the `count - j` ASIDs still to take free. -/
structure RetypeWindowFrame (st : SystemState) (src dst : CSpaceAddr) (childId U : SeLe4n.ObjId)
    (req : CarveRequest) (count : Nat) (ut0 : UntypedObject) (a0 j : Nat) (s : SystemState)
    (cap : Capability) (ut : UntypedObject) : Prop where
  asidInv : s.asidTable.invExt
  lookup : SystemState.lookupSlotCap s src = some cap
  target : cap.target = .object U
  authority : lifecycleRetypeAuthority cap U = true
  untyped : s.getUntyped? U = some ut
  base : ut.regionBase = ut0.regionBase
  regionSize : ut.regionSize = ut0.regionSize
  isDevice : ut.isDevice = ut0.isDevice
  reset : retypeResetAdmitted s src ut = true
  index : alignedCarveIndex req.objectType req.size ut (retypeFreeIndex s src cap) = a0 + j * req.size
  kids : ∀ m, j ≤ m → m < count → childrenNameNone (retypeChildId childId m) ut.children = true
  slots : ∀ m, j ≤ m → m < count → cspaceDstAdmitted (retypeChildSlot dst m) s = true
  fresh : ∀ m, j ≤ m → m < count → s.objects[retypeChildId childId m]? = none
  grow : RetypeTablesGrow st s j
  asidSize : s.asidTable.size ≤ st.asidTable.size + j
  asids : req.windowAdmissible s (count - j) = true

/-- **Carve `j` of an admitted window is admitted, and leaves what carve
`j + 1` reads.** -/
theorem RetypeWindowFrame.step {st s : SystemState} {src dst : CSpaceAddr}
    {childId U : SeLe4n.ObjId} {req : CarveRequest} {count : Nat} {ut0 : UntypedObject}
    {a0 j : Nat} {cap : Capability} {ut : UntypedObject}
    (C : RetypeWindowChecks st childId U req count ut0 a0)
    (F : RetypeWindowFrame st src dst childId U req count ut0 a0 j s cap ut) (hj : j < count) :
    untypedRetypeAdmittedAt s src (retypeChildSlot dst j) (retypeChildId childId j)
        (req.atState s) = true ∧
      RetypeWindowFrame st src dst childId U req count ut0 a0 (j + 1)
        (untypedRetypePerformAt src (retypeChildSlot dst j) (retypeChildId childId j)
          (req.atState s) s)
        (cap.withFreeIndex (a0 + j * req.size + req.size))
        (ut.allocated (a0 + j * req.size) (retypeChildId childId j) req.size) := by
  have hIdx : (req.atState s).carveIndex ut (retypeFreeIndex s src cap) = a0 + j * req.size := by
    unfold CarveRequest.carveIndex
    rw [CarveRequest.atState_objectType, CarveRequest.atState_size]; exact F.index
  have hSz := CarveRequest.atState_size s req
  obtain ⟨hIdU, hIrq, hAddr⟩ := C.ids j hj
  -- The ASID a VSpace root takes here.
  have hRoot : ∀ a, req = .vspaceRoot a → ∃ a', freshAsid? s = some a' ∧
      req.atState s = .vspaceRoot a' := by
    intro a hr
    have hA := F.asids
    rw [hr] at hA
    simp only [CarveRequest.windowAdmissible] at hA
    rw [show count - j = (count - j - 1) + 1 by omega] at hA
    obtain ⟨a', ha'⟩ := freshAsidsFrom_some s _ _ _ hA
    exact ⟨a', ha', by rw [hr]; simp only [CarveRequest.atState]; unfold freshAsid?; rw [ha']; rfl⟩
  refine ⟨?_, ?_⟩
  · -- The admission.
    unfold untypedRetypeAdmittedAt
    rw [F.lookup]
    simp only [F.target, F.untyped, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, F.slots j (Nat.le_refl j) hj, ?_⟩
    · unfold CarveRequest.heapAdmitted
      rw [decide_eq_true_eq, F.grow.heap]
      exact Nat.le_trans (CarveRequest.heapBytes_atState_le_window (by omega)
        (rhInsertResizeHeapBytes_le_window F.grow.objSize hj F.grow.objCap)
        (rhInsertResizeHeapBytes_le_window F.asidSize hj F.grow.asidCap)) C.heap
    · cases hr : req
      case vspaceRoot a =>
        obtain ⟨a', ha', hAt⟩ := hRoot a hr
        rw [← hr, hAt]
        obtain ⟨h1, h2, h3⟩ := freshAsidFrom_spec s _ _ _ ha'
        simp only [CarveRequest.admissible, Bool.and_eq_true, bne_iff_ne, ne_eq,
          decide_eq_true_eq]
        exact ⟨⟨by omega, h2⟩, h3⟩
      all_goals rfl
    · unfold retypeFromUntypedAdmitted
      rw [CarveRequest.atState_objectType, hSz]
      have hRA : retypeResetAdmitted s { cnode := src.cnode, slot := src.slot } ut = true := F.reset
      have hFI : retypeFreeIndex s { cnode := src.cnode, slot := src.slot } cap =
          retypeFreeIndex s src cap := rfl
      rw [hFI, F.index]
      have hS := F.grow.objSize
      have hW : objectIdInAddressSpace s.machine (retypeChildId childId j) = true := by
        unfold objectIdInAddressSpace at hAddr ⊢; rw [F.grow.width]; exact hAddr
      have hFr : (s.getObject? (retypeChildId childId j)).isSome = false := by
        unfold SystemState.getObject?; rw [F.fresh j (Nat.le_refl j) hj]; rfl
      have hCan : ut.canAllocate (a0 + j * req.size) req.size = true := by
        unfold UntypedObject.canAllocate
        have hm : (j + 1) * req.size ≤ count * req.size := Nat.mul_le_mul_right _ hj
        rw [Nat.succ_mul] at hm
        simp only [Bool.and_eq_true, decide_eq_true_eq, F.regionSize]
        exact ⟨C.sizePos, by have := C.fits; omega⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, hFr, hIrq,
        Bool.or_false, F.kids j (Nat.le_refl j) hj, F.isDevice, C.device, hW, F.authority, hRA,
        hCan, and_true]
      refine ⟨⟨by have := C.capacity; omega, hIdU⟩, C.allocSize⟩
  · -- What the carve leaves.
    obtain ⟨g, hL', hC', hU', hSlots', hFresh', hAsid'⟩ :=
      untypedRetypePerformAt_frame (req := req.atState s) F.grow.objInv F.lookup F.target
        F.untyped (F.slots j (Nat.le_refl j) hj) (F.fresh j (Nat.le_refl j) hj)
    rw [hIdx, hSz] at hL' hU'
    have hChildNe : ∀ m, j < m → retypeChildId childId m ≠ retypeChildId childId j := by
      intro m hm h
      have := SeLe4n.ObjId.ofNat_injective h; omega
    have hAsidAt : ∀ x, (∀ a, req.atState s = .vspaceRoot a → x ≠ a) →
        (untypedRetypePerformAt src (retypeChildSlot dst j) (retypeChildId childId j)
          (req.atState s) s).asidTable[x]? = s.asidTable[x]? := by
      intro x hx
      rw [hAsid']
      cases hr : req.atState s
      case vspaceRoot a =>
        exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _
          (fun h => hx a hr (eq_of_beq h).symm) F.asidInv
      all_goals rfl
    refine
      { asidInv := ?_, lookup := hL', target := F.target, authority := F.authority,
        untyped := hU', base := F.base, regionSize := F.regionSize, isDevice := F.isDevice,
        reset := ?_, index := ?_, kids := ?_, slots := ?_, fresh := ?_,
        grow := F.grow.trans g, asidSize := ?_, asids := ?_ }
    · rw [hAsid']
      cases req.atState s
      case vspaceRoot a => exact RHTable_insert_preserves_invExt _ _ _ F.asidInv
      all_goals exact F.asidInv
    · unfold retypeResetAdmitted; rw [hC']; rfl
    · unfold retypeFreeIndex; rw [hC']
      simp only [ite_true, Capability.withFreeIndex_freeIndex]
      have hA : ((ut.allocated (a0 + j * req.size) (retypeChildId childId j) req.size).regionBase.toNat
          + a0) % carveAlignment req.objectType req.size = 0 := by
        show (ut.regionBase.toNat + a0) % _ = 0
        rw [F.base]; exact C.aligned
      rw [show a0 + j * req.size + req.size = a0 + (j + 1) * req.size by rw [Nat.succ_mul]; omega]
      exact alignedCarveIndex_window req _ hA (j + 1)
    · intro m hm hmc
      show childrenNameNone _ ({ objId := retypeChildId childId j, offset := _, size := _ } ::
        ut.children) = true
      unfold childrenNameNone
      have hne : (retypeChildId childId j == retypeChildId childId m) = false := by
        simp only [beq_eq_false_iff_ne]; exact Ne.symm (hChildNe m (by omega))
      simp only [hne]
      exact F.kids m (by omega) hmc
    · intro m hm hmc
      apply hSlots' (retypeChildSlot dst m) rfl _ (F.slots m (by omega) hmc)
      intro h
      have := SeLe4n.Slot.ofNat_injective h; omega
    · intro m hm hmc
      exact hFresh' _ (hChildNe m (by omega)) (F.fresh m (by omega) hmc)
    · rw [hAsid']
      cases req.atState s
      case vspaceRoot a =>
        exact Nat.le_trans (RobinHood.RHTable.size_insert_le _ _ _ F.asidInv.1)
          (by have := F.asidSize; omega)
      all_goals exact Nat.le_trans F.asidSize (by omega)
    · by_cases hv : ∃ a, req = .vspaceRoot a
      · obtain ⟨a, hr⟩ := hv
        obtain ⟨a', ha', hAt⟩ := hRoot a hr
        have hW : ∀ t n, req.windowAdmissible t n = freshAsidsFrom t t.machine.maxASID 1 n := by
          intro t n; rw [hr]; rfl
        have hA := F.asids
        rw [hW, show count - j = (count - (j + 1)) + 1 by omega] at hA
        rw [hW, g.maxAsid]
        refine freshAsidsFrom_step g.maxAsid (fun m hm hfree => ?_) _ _ _ hA ha'
        rw [hAsidAt _ (fun b hb => by
          rw [hAt] at hb; cases hb
          intro he; apply hm; rw [← he]; rfl)]
        exact hfree
      · have hW : ∀ t n, req.windowAdmissible t n = true := by
          intro t n
          cases hr : req
          case vspaceRoot a => exact absurd ⟨a, hr⟩ hv
          all_goals rfl
        exact hW _ _

/-- **Carves from a frame are the window's carves**: from carve `j` on, every
carve's admission holds, so the writes are the unguarded carves. -/
theorem untypedRetypeWindowWrites_eq_carves_of_frame {st : SystemState} {src dst : CSpaceAddr}
    {childId U : SeLe4n.ObjId} {req : CarveRequest} {count : Nat} {ut0 : UntypedObject} {a0 : Nat}
    (C : RetypeWindowChecks st childId U req count ut0 a0) :
    ∀ (k j : Nat) (s : SystemState) (cap : Capability) (ut : UntypedObject), j + k = count →
      RetypeWindowFrame st src dst childId U req count ut0 a0 j s cap ut →
      untypedRetypeWindowWrites src dst childId req j k s =
        untypedRetypeWindowCarves src dst childId req j k s
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, j, s, cap, ut, hjk, F => by
    obtain ⟨hA, F'⟩ := F.step C (by omega)
    unfold untypedRetypeWindowWrites untypedRetypeWindowCarves
    rw [if_pos hA]
    exact untypedRetypeWindowWrites_eq_carves_of_frame C k (j + 1) _ _ _ (by omega) F'

/-- **What an admitted window's checks say, at the state it was handed**: the
checks every carve shares, and the first carve's frame. -/
theorem untypedRetypeWindowRefusal_none_frame {st : SystemState} {src dst : CSpaceAddr}
    {childId : SeLe4n.ObjId} {req : CarveRequest} {count : Nat}
    (hInv : st.objects.invExt) (hAsid : st.asidTable.invExt)
    (h : untypedRetypeWindowRefusal st src dst childId req count = none) :
    ∃ (U : SeLe4n.ObjId) (ut0 : UntypedObject) (cap : Capability) (a0 : Nat),
      RetypeWindowChecks st childId U req count ut0 a0 ∧
      RetypeWindowFrame st src dst childId U req count ut0 a0 0 st cap ut0 := by
  unfold untypedRetypeWindowRefusal untypedRetypeWindowRefusalWith at h
  cases hL : SystemState.lookupSlotCap st src with
  | none =>
    rw [hL] at h
    cases hC : st.getCNode? src.cnode <;> rw [hC] at h <;> cases h
  | some cap =>
    rw [hL] at h
    dsimp only at h
    cases hT : cap.target with
    | object U =>
      rw [hT] at h
      dsimp only at h
      cases hAu : lifecycleRetypeAuthority cap U
      · simp [hAu] at h
      simp only [hAu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hU : st.getUntyped? U with
      | none => rw [hU] at h; simp at h
      | some ut =>
        rw [hU] at h
        dsimp only at h
        cases hSl : retypeWindowSlotsRefusal st dst.cnode dst.slot 0 count with
        | some e => rw [hSl] at h; simp at h
        | none =>
          rw [hSl] at h
          dsimp only at h
          split at h
          · cases h
          next hR =>
          split at h
          · cases h
          next hCan =>
          split at h
          · cases h
          next hDev =>
          split at h
          · cases h
          next hAl =>
          cases hId : retypeWindowIdsRefusal st U childId ut 0 count with
          | some e => rw [hId] at h; simp at h
          | none =>
            rw [hId] at h
            dsimp only at h
            split at h
            · cases h
            next hCap =>
            split at h
            · cases h
            next hAs =>
            split at h
            · cases h
            next hHeap =>
            have hR' : retypeResetAdmitted st src ut = true := by simpa using hR
            have hAs' : req.windowAdmissible st count = true := by simpa using hAs
            have hHeap' : req.windowHeapBytes st count ≤ st.machine.kernelHeapFreeBytes := by
              simpa using hHeap
            have hDev' := Bool.eq_false_iff.mpr hDev
            have hCan' : ut.canAllocate (alignedCarveIndex req.objectType req.size ut
                (retypeFreeIndex st src cap)) (count * req.size) = true := by simpa using hCan
            simp only [UntypedObject.canAllocate, Bool.and_eq_true, decide_eq_true_eq] at hCan'
            obtain ⟨hPos, hFits⟩ := hCan'
            have hSize : 0 < req.size := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hPos; simp at hPos)
            have hCount : 0 < count := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hPos; simp at hPos)
            refine ⟨U, ut, cap, alignedCarveIndex req.objectType req.size ut
              (retypeFreeIndex st src cap), ?_, ?_⟩
            · refine ⟨fun m hm => ?_, hDev', hAl, hSize, hFits,
                alignedCarveIndex_aligned _ hSize _ _, by omega, ?_⟩
              · obtain ⟨h1, -, h3, -, h5⟩ := retypeWindowIdsRefusal_none hId m hm
                rw [Nat.zero_add] at h1 h3 h5
                exact ⟨h1, h3, h5⟩
              · exact hHeap'
            · refine
                { asidInv := hAsid, lookup := hL, target := hT, authority := hAu, untyped := hU,
                  base := rfl, regionSize := rfl, isDevice := rfl, reset := hR',
                  index := by simp, kids := fun m _ hm => ?_, slots := fun m _ hm => ?_,
                  fresh := fun m _ hm => ?_,
                  grow := RetypeTablesGrow.of_objects_eq hInv rfl rfl rfl 0,
                  asidSize := Nat.le_refl _, asids := by simpa using hAs' }
              · have := (retypeWindowIdsRefusal_none hId m hm).2.2.2.1
                rwa [Nat.zero_add] at this
              · have := retypeWindowSlotsRefusal_none hSl m hm
                rwa [Nat.zero_add] at this
              · have := (retypeWindowIdsRefusal_none hId m hm).2.1
                rwa [Nat.zero_add] at this
    | _ => rw [hT] at h; simp at h

/-- **WS-SX SX6.3 (D9): an admitted window admits every carve.**  On a store
whose object and ASID tables are well formed, a window that
`untypedRetypeWindowRefusal` admits makes every one of its `count` carves:
each carve's own admission (`untypedRetypeAdmittedAt`), read at the state the
carves before it left, holds, so `untypedRetypeWindowWrites` never stops early
and its writes are the window's carves (`untypedRetypeWindowCarves`), as seL4's
`invokeUntyped_Retype` cannot fail once `decodeUntypedInvocation` has
admitted the call. -/
theorem untypedRetypeWindow_admitsEveryCarve {st : SystemState} {src dst : CSpaceAddr}
    {childId : SeLe4n.ObjId} {req : CarveRequest} {count : Nat}
    (hInv : st.objects.invExt) (hAsid : st.asidTable.invExt)
    (h : untypedRetypeWindowRefusal st src dst childId req count = none) :
    untypedRetypeWindowWrites src dst childId req 0 count st =
      untypedRetypeWindowCarves src dst childId req 0 count st := by
  obtain ⟨_, _, _, _, C, F⟩ := untypedRetypeWindowRefusal_none_frame hInv hAsid h
  exact untypedRetypeWindowWrites_eq_carves_of_frame C count 0 st _ _ (by omega) F

end SeLe4n.Kernel
