-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.DeliveryCommute
import SeLe4n.Kernel.IPC.DualQueue.WithCaps

/-!
# A capability transfer commutes with a thread's message write

seL4's `transferCaps` reads CNodes, untypeds, VSpace roots and the slots'
derivation links, and writes a CNode, the links, the derivation tree and the
physical-write ledger.  A thread write that leaves the thread's space-slot
links alone (a delivery's message slots, a return frame) touches none of
those, so on an object table with no resize due the two commute: the transfer
reads the same and writes the same whichever runs first
(`receiveTransferCaps_mapTcbInPlace`).  The in-place arms use this to run the
transfer after the rendezvous they write in place and before the frame they
stage, as the specification orders them, without holding the message.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood

/-- **A thread write a transfer cannot see**: it keeps the thread's space-slot
link words and commutes with their writes. -/
structure LinkBlindWrite (G : TCB → TCB) : Prop where
  setLinks : ∀ t s f c w, G (t.setSpaceLinkWords s f c w) = (G t).setSpaceLinkWords s f c w
  nodeWord : ∀ t s f, (G t).spaceLinkNodeWord s f = t.spaceLinkNodeWord s f
  slotWord : ∀ t s f, (G t).spaceLinkSlotWord s f = t.spaceLinkSlotWord s f

/-- A message-slot write is one. -/
theorem LinkBlindWrite.withMessageSlots (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat) :
    LinkBlindWrite (TCB.withMessageSlots ρ μ π) :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

section

variable {G : TCB → TCB} (hG : LinkBlindWrite G) (x : SeLe4n.ThreadId)

/-- A read of one object through the write, for a read the write cannot see. -/
theorem objects_read_mapTcbInPlace {α : Type} (Z : SystemState) (k : SeLe4n.ObjId)
    (f : Option KernelObject → α) (hf : ∀ t, f (some (.tcb (G t))) = f (some (.tcb t))) :
    f ((Z.mapTcbInPlace x G).objects[k]?) = f (Z.objects[k]?) := by
  rw [SystemState.objects_mapTcbInPlace]
  split
  · cases Z.objects[k]? with
    | none => rfl
    | some o => cases o <;> first | rfl | exact hf _
  · rfl

theorem getCNode?_mapTcbInPlace_blind (Z : SystemState) (k : SeLe4n.ObjId) :
    (Z.mapTcbInPlace x G).getCNode? k = Z.getCNode? k :=
  objects_read_mapTcbInPlace (G := G) x Z k (fun o => match o with
    | some (.cnode cn) => some cn | _ => none) (fun _ => rfl)

theorem lookupCNode_mapTcbInPlace_blind (Z : SystemState) (k : SeLe4n.ObjId) :
    SystemState.lookupCNode (Z.mapTcbInPlace x G) k = SystemState.lookupCNode Z k :=
  objects_read_mapTcbInPlace (G := G) x Z k (fun o => match o with
    | some (.cnode cn) => some cn | _ => none) (fun _ => rfl)

theorem lookupSlotCap_mapTcbInPlace_blind (Z : SystemState) (ref : SlotRef) :
    SystemState.lookupSlotCap (Z.mapTcbInPlace x G) ref = SystemState.lookupSlotCap Z ref := by
  unfold SystemState.lookupSlotCap
  rw [lookupCNode_mapTcbInPlace_blind (G := G) x]

theorem getUntyped?_mapTcbInPlace_blind (Z : SystemState) (k : SeLe4n.ObjId) :
    (Z.mapTcbInPlace x G).getUntyped? k = Z.getUntyped? k :=
  objects_read_mapTcbInPlace (G := G) x Z k (fun o => match o with
    | some (.untyped u) => some u | _ => none) (fun _ => rfl)

theorem getVSpaceRoot?_mapTcbInPlace_blind (Z : SystemState) (k : SeLe4n.ObjId) :
    (Z.mapTcbInPlace x G).getVSpaceRoot? k = Z.getVSpaceRoot? k :=
  objects_read_mapTcbInPlace (G := G) x Z k (fun o => match o with
    | some (.vspaceRoot r) => some r | _ => none) (fun _ => rfl)

include hG in
theorem slotLinkNodeWord_mapTcbInPlace_blind (Z : SystemState) (o : SeLe4n.ObjId)
    (s : SeLe4n.Slot) (f : LinkField) :
    (Z.mapTcbInPlace x G).slotLinkNodeWord o s f = Z.slotLinkNodeWord o s f := by
  rw [SystemState.slotLinkNodeWord_def, SystemState.slotLinkNodeWord_def]
  exact objects_read_mapTcbInPlace (G := G) x Z o (fun ob => match ob with
    | some ob => ob.linkNodeWord s f | none => 0) (fun t => hG.nodeWord t s f)

include hG in
theorem slotLinkSlotWord_mapTcbInPlace_blind (Z : SystemState) (o : SeLe4n.ObjId)
    (s : SeLe4n.Slot) (f : LinkField) :
    (Z.mapTcbInPlace x G).slotLinkSlotWord o s f = Z.slotLinkSlotWord o s f := by
  rw [SystemState.slotLinkSlotWord_def, SystemState.slotLinkSlotWord_def]
  exact objects_read_mapTcbInPlace (G := G) x Z o (fun ob => match ob with
    | some ob => ob.linkSlotWord s f | none => 0) (fun t => hG.slotWord t s f)

end

/-! ## The writes -/

section

variable {G : TCB → TCB} (hG : LinkBlindWrite G) (x : SeLe4n.ThreadId)

/-- An object update that commutes with the thread write on every object
commutes with it on the state. -/
theorem modifyObject_mapTcbInPlace_comm (Z : SystemState) (o : SeLe4n.ObjId)
    (F : KernelObject → KernelObject) (hNo : Z.objects.noResizeDue)
    (hc : ∀ ob, F (KernelObject.mapTcb G ob) = KernelObject.mapTcb G (F ob)) :
    (Z.mapTcbInPlace x G).modifyObject o F = (Z.modifyObject o F).mapTcbInPlace x G := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo,
    SystemState.modifyObject_eq_mapValueAt (Z.mapTcbInPlace x G) _ _ hNo]
  exact SystemState.mapTcbInPlace_swap_objects Z x G o F (fun _ ob => hc ob)

/-- The ledger and the thread write touch different fields. -/
theorem recordPhysicalWrites_mapTcbInPlace (Z : SystemState)
    (ws : List Architecture.PhysicalWrite) :
    Architecture.recordPhysicalWrites (Z.mapTcbInPlace x G) ws =
      (Architecture.recordPhysicalWrites Z ws).mapTcbInPlace x G := rfl

theorem modifyCdt_mapTcbInPlace (Z : SystemState) (f : CapDerivationTree → CapDerivationTree) :
    (Z.mapTcbInPlace x G).modifyCdt f = (Z.modifyCdt f).mapTcbInPlace x G := rfl

include hG

omit hG in
/-- Under no resize, a link write is the object update it makes: an object
with no slots is left as it is by that update. -/
theorem setSlotLinkWords_eq_modifyObject (Z : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) (c w : Nat) (hNo : Z.objects.noResizeDue) :
    Z.setSlotLinkWords o s f c w = Z.modifyObject o (·.setLinkWords s f c w) := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
  unfold SystemState.setSlotLinkWords SystemState.getObject?
  cases hZ : Z.objects[o]? with
  | none =>
    have hg : Z.objects.get? o = none := by simpa only [RHTable_getElem?_eq_get?] using hZ
    rw [RHTable.mapValueAt_of_get?_none hg]
  | some ob =>
    have hg : Z.objects.get? o = some ob := by simpa only [RHTable_getElem?_eq_get?] using hZ
    cases ob
    case cnode => simp only []; rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
    case tcb => simp only []; rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
    all_goals
      simp only []
      rw [RHTable.mapValueAt_congr hg (F := fun ob => KernelObject.setLinkWords ob s f c w)
        (G := id) rfl, RHTable.mapValueAt_id]

/-- A link write commutes with the thread write. -/
theorem setSlotLinkWords_mapTcbInPlace (Z : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) (c w : Nat) (hNo : Z.objects.noResizeDue) :
    (Z.mapTcbInPlace x G).setSlotLinkWords o s f c w =
      (Z.setSlotLinkWords o s f c w).mapTcbInPlace x G := by
  have hc : ∀ ob, KernelObject.setLinkWords (KernelObject.mapTcb G ob) s f c w =
      KernelObject.mapTcb G (KernelObject.setLinkWords ob s f c w) := by
    intro ob; cases ob <;> try rfl
    simp only [KernelObject.mapTcb, KernelObject.setLinkWords, hG.setLinks]
  rw [setSlotLinkWords_eq_modifyObject _ _ _ _ _ _ hNo,
    setSlotLinkWords_eq_modifyObject (Z.mapTcbInPlace x G) _ _ _ _ _ hNo]
  exact modifyObject_mapTcbInPlace_comm x Z o (fun ob => ob.setLinkWords s f c w) hNo hc

omit hG in
theorem setSlotLinkWords_noResizeDue (Z : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) (c w : Nat) (hNo : Z.objects.noResizeDue) :
    (Z.setSlotLinkWords o s f c w).objects.noResizeDue := by
  rw [setSlotLinkWords_eq_modifyObject _ _ _ _ _ _ hNo,
    SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
  exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo

theorem linkAddChild_mapTcbInPlace (Z : SystemState) (p c : SlotRef)
    (hNo : Z.objects.noResizeDue) :
    (Z.mapTcbInPlace x G).linkAddChild p c = (Z.linkAddChild p c).mapTcbInPlace x G := by
  unfold SystemState.linkAddChild
  simp only [slotLinkNodeWord_mapTcbInPlace_blind hG, slotLinkSlotWord_mapTcbInPlace_blind hG]
  have h1 := setSlotLinkWords_noResizeDue Z c.cnode c.slot .parent (p.cnode.toNat + 1)
    (p.slot.toNat + 1) hNo
  rw [setSlotLinkWords_mapTcbInPlace hG x _ _ _ _ _ _ hNo]
  generalize Z.setSlotLinkWords c.cnode c.slot .parent (p.cnode.toNat + 1) (p.slot.toNat + 1)
    = Zp at h1
  have h2 := setSlotLinkWords_noResizeDue Zp c.cnode c.slot .next
    (Z.slotLinkNodeWord p.cnode p.slot .firstChild)
    (Z.slotLinkSlotWord p.cnode p.slot .firstChild) h1
  rw [setSlotLinkWords_mapTcbInPlace hG x _ _ _ _ _ _ h1]
  generalize Zp.setSlotLinkWords c.cnode c.slot .next _ _ = Zq at h2
  have h3 := setSlotLinkWords_noResizeDue Zq c.cnode c.slot .prev 0 0 h2
  rw [setSlotLinkWords_mapTcbInPlace hG x _ _ _ _ _ _ h2]
  generalize Zq.setSlotLinkWords c.cnode c.slot .prev 0 0 = Zr at h3
  split
  · exact setSlotLinkWords_mapTcbInPlace hG x _ _ _ _ _ _ h3
  · have h4 := setSlotLinkWords_noResizeDue Zr
      (SeLe4n.ObjId.ofNat (Z.slotLinkNodeWord p.cnode p.slot .firstChild - 1))
      (SeLe4n.Slot.ofNat (Z.slotLinkSlotWord p.cnode p.slot .firstChild - 1)) .prev
      (c.cnode.toNat + 1) (c.slot.toNat + 1) h3
    rw [setSlotLinkWords_mapTcbInPlace hG x _ _ _ _ _ _ h3,
      setSlotLinkWords_mapTcbInPlace hG x _ _ _ _ _ _ h4]

omit hG in
theorem linkAddChild_noResizeDue (Z : SystemState) (p c : SlotRef)
    (hNo : Z.objects.noResizeDue) : (Z.linkAddChild p c).objects.noResizeDue := by
  unfold SystemState.linkAddChild
  dsimp only
  split <;> (repeat apply setSlotLinkWords_noResizeDue) <;> exact hNo

theorem cdtAddChild_mapTcbInPlace (Z : SystemState) (p c : SlotRef) (op : DerivationOp)
    (hNo : Z.objects.noResizeDue) :
    (Z.mapTcbInPlace x G).cdtAddChild p c op = (Z.cdtAddChild p c op).mapTcbInPlace x G := by
  unfold SystemState.cdtAddChild
  rw [modifyCdt_mapTcbInPlace]
  exact linkAddChild_mapTcbInPlace hG x _ p c hNo

omit hG in
theorem cdtAddChild_noResizeDue (Z : SystemState) (p c : SlotRef) (op : DerivationOp)
    (hNo : Z.objects.noResizeDue) : (Z.cdtAddChild p c op).objects.noResizeDue :=
  linkAddChild_noResizeDue _ p c hNo

end

/-! ## Stores over a CNode -/

/-- An insert at a present key commutes with a slot write that keeps the
inserted value. -/
theorem RHTable.insert_mapValueAt_comm {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (x k : α) (F : β → β) (v obj : β) (hNo : t.noResizeDue)
    (hk : t.get? k = some v) (hF : F obj = obj) :
    (t.mapValueAt x F).insert k obj = (t.insert k obj).mapValueAt x F := by
  have hk' : (t.mapValueAt x F).get? k = some (if x == k then F v else v) := by
    rw [RHTable.get?_mapValueAt, hk]; split <;> rfl
  rw [RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? hNo hk),
    RHTable.insert_eq_mapValueAt _
      (RHTable.findsInPlace_of_get? ((RHTable.noResizeDue_mapValueAt t x F).mpr hNo) hk')]
  by_cases hx : x = k
  · subst hx
    rw [RHTable.mapValueAt_mapValueAt, RHTable.mapValueAt_mapValueAt]
    congr 1; funext _; simp [hF]
  · exact (RHTable.mapValueAt_comm _ _ _ hx).symm

section

variable {G : TCB → TCB} (x : SeLe4n.ThreadId)

/-- A store of a CNode over a CNode commutes with the thread write. -/
theorem storeObject_cnode_mapTcbInPlace (Z : SystemState) (k : SeLe4n.ObjId) (cn0 cn : CNode)
    (hk : Z.objects[k]? = some (.cnode cn0)) (hNo : Z.objects.noResizeDue) :
    storeObject k (.cnode cn) (Z.mapTcbInPlace x G) =
      .ok ((), (match storeObject k (.cnode cn) Z with
        | .ok ((), Z') => Z' | .error _ => Z).mapTcbInPlace x G) := by
  have hk' : (Z.mapTcbInPlace x G).objects[k]? = some (.cnode cn0) := by
    rw [SystemState.objects_mapTcbInPlace, hk]; split <;> rfl
  have hg : Z.objects.get? k = some (.cnode cn0) := by
    simpa only [RHTable_getElem?_eq_get?] using hk
  unfold storeObject
  simp only [hk, hk']
  unfold SystemState.mapTcbInPlace
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
  rw [RHTable.insert_mapValueAt_comm _ _ _ _ _ _ hNo hg rfl]
  rfl

theorem storeObject_cnode_noResizeDue (Z : SystemState) (k : SeLe4n.ObjId) (cn0 cn : CNode)
    (hk : Z.objects[k]? = some (.cnode cn0)) (hNo : Z.objects.noResizeDue) (Z' : SystemState)
    (h : storeObject k (.cnode cn) Z = .ok ((), Z')) : Z'.objects.noResizeDue := by
  have hg : Z.objects.get? k = some (.cnode cn0) := by
    simpa only [RHTable_getElem?_eq_get?] using hk
  unfold storeObject at h
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
  rw [← h]
  show (Z.objects.insert k _).noResizeDue
  rw [RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? hNo hg)]
  exact hNo

theorem storeLeavesIndexAndTypes_mapTcbInPlace (Z : SystemState) (k : SeLe4n.ObjId)
    (ty : KernelObjectType) (cn0 : CNode) (hk : Z.objects[k]? = some (.cnode cn0)) :
    storeLeavesIndexAndTypes (Z.mapTcbInPlace x G) k ty =
      storeLeavesIndexAndTypes Z k ty := by
  have hk' : (Z.mapTcbInPlace x G).objects[k]? = some (.cnode cn0) := by
    rw [SystemState.objects_mapTcbInPlace, hk]; split <;> rfl
  unfold storeLeavesIndexAndTypes
  rw [hk, hk']; rfl

omit G x in
theorem storeCNodeWith_of_not_cnode (Z : SystemState) (k : SeLe4n.ObjId) (f : CNode → CNode)
    (h : ∀ cn, Z.objects[k]? ≠ some (.cnode cn)) : Z.storeCNodeWith k f = Z := by
  rcases SystemState.storeCNodeWith_cases Z k f with ⟨cn, hk, -⟩ | e
  · exact absurd hk (h cn)
  · exact e

/-- `storeCNodeWith` commutes with the thread write. -/
theorem storeCNodeWith_mapTcbInPlace (Z : SystemState) (k : SeLe4n.ObjId) (f : CNode → CNode)
    (hNo : Z.objects.noResizeDue) :
    (Z.mapTcbInPlace x G).storeCNodeWith k f = (Z.storeCNodeWith k f).mapTcbInPlace x G := by
  cases hk : Z.objects[k]? with
  | none =>
    have hk' : (Z.mapTcbInPlace x G).objects[k]? = none := by
      rw [SystemState.objects_mapTcbInPlace, hk]; split <;> rfl
    unfold SystemState.storeCNodeWith; rw [hk, hk']
  | some ob =>
    cases ob
    case cnode cn0 =>
      have hk' : (Z.mapTcbInPlace x G).objects[k]? = some (.cnode cn0) := by
        rw [SystemState.objects_mapTcbInPlace, hk]; split <;> rfl
      unfold SystemState.storeCNodeWith
      rw [hk, hk', storeLeavesIndexAndTypes_mapTcbInPlace x Z k _ cn0 hk]
      dsimp only
      split
      · exact modifyObject_mapTcbInPlace_comm x Z k _ hNo (fun ob => by cases ob <;> rfl)
      · rw [storeObject_cnode_mapTcbInPlace x Z k cn0 (f cn0) hk hNo]
        cases storeObject k (.cnode (f cn0)) Z <;> rfl
    all_goals
      have hne : ∀ cn, Z.objects[k]? ≠ some (.cnode cn) := by intro cn h; rw [hk] at h; cases h
      have hne' : ∀ cn, (Z.mapTcbInPlace x G).objects[k]? ≠ some (.cnode cn) := by
        intro cn h
        rw [SystemState.objects_mapTcbInPlace, hk] at h
        split at h <;> simp [KernelObject.mapTcb] at h
      rw [storeCNodeWith_of_not_cnode _ _ _ hne, storeCNodeWith_of_not_cnode _ _ _ hne']

theorem storeCNodeWith_noResizeDue (Z : SystemState) (k : SeLe4n.ObjId) (f : CNode → CNode)
    (hNo : Z.objects.noResizeDue) : (Z.storeCNodeWith k f).objects.noResizeDue := by
  rcases SystemState.storeCNodeWith_cases Z k f with ⟨cn, hk, hS⟩ | e
  · exact storeObject_cnode_noResizeDue Z k cn (f cn) hk hNo _ hS
  · rw [e]; exact hNo

end

/-! ## One capability's install, and the transfer -/

/-- A step's result with the thread write applied to its state. -/
@[inline] def mapStepState {α : Type} (x : SeLe4n.ThreadId) (G : TCB → TCB) :
    Except KernelError (α × SystemState) → Except KernelError (α × SystemState)
  | .ok (a, Z') => .ok (a, Z'.mapTcbInPlace x G)
  | .error e => .error e

section

variable {G : TCB → TCB} (hG : LinkBlindWrite G) (x : SeLe4n.ThreadId)

theorem setCapFreeIndex_mapTcbInPlace (Z : SystemState) (addr : CSpaceAddr) (idx : Nat)
    (hNo : Z.objects.noResizeDue) :
    setCapFreeIndex (Z.mapTcbInPlace x G) addr idx = (setCapFreeIndex Z addr idx).mapTcbInPlace x G :=
  storeCNodeWith_mapTcbInPlace x Z addr.cnode _ hNo

theorem untypedSourceSetFull_mapTcbInPlace (Z : SystemState) (src : CSpaceAddr) (cap : Capability)
    (hNo : Z.objects.noResizeDue) :
    untypedSourceSetFull (Z.mapTcbInPlace x G) src cap =
      (untypedSourceSetFull Z src cap).mapTcbInPlace x G := by
  unfold untypedSourceSetFull
  split
  · rw [getUntyped?_mapTcbInPlace_blind (G := G) x]
    split
    · exact setCapFreeIndex_mapTcbInPlace x Z src _ hNo
    · rfl
  · rfl

theorem untypedSourceSetFull_noResizeDue (Z : SystemState) (src : CSpaceAddr) (cap : Capability)
    (hNo : Z.objects.noResizeDue) : (untypedSourceSetFull Z src cap).objects.noResizeDue :=
  untypedSourceSetFull_of (P := fun s => s.objects.noResizeDue) hNo
    (fun _ => storeCNodeWith_noResizeDue _ _ _ hNo)

theorem cspaceInsertSlot_mapTcbInPlace (dst : CSpaceAddr) (cap : Capability) (Z : SystemState)
    (hNo : Z.objects.noResizeDue) :
    cspaceInsertSlot dst cap (Z.mapTcbInPlace x G) =
      mapStepState x G (cspaceInsertSlot dst cap Z) := by
  unfold cspaceInsertSlot
  rw [getCNode?_mapTcbInPlace_blind (G := G) x]
  cases hC : Z.getCNode? dst.cnode with
  | none => rfl
  | some cn =>
    simp only []
    split
    · rfl
    · split
      · rfl
      · have hk := (SystemState.getCNode?_eq_some_iff Z dst.cnode cn).mp hC
        rw [storeObject_cnode_mapTcbInPlace x Z dst.cnode cn _ hk hNo]
        rcases storeObject_isOk Z dst.cnode (.cnode (cn.insert dst.slot cap)) with ⟨Z', hS⟩
        rw [hS]; rfl

theorem cspaceInsertSlot_noResizeDue (dst : CSpaceAddr) (cap : Capability) (Z Z' : SystemState)
    (hNo : Z.objects.noResizeDue) (h : cspaceInsertSlot dst cap Z = .ok ((), Z')) :
    Z'.objects.noResizeDue := by
  obtain ⟨cn, hC, -, -, hS⟩ := cspaceInsertSlot_ok_decompose Z Z' dst cap h
  exact storeObject_cnode_noResizeDue Z dst.cnode cn _
    ((SystemState.getCNode?_eq_some_iff Z dst.cnode cn).mp hC) hNo Z' hS

include hG in
theorem untypedDeriveRefused_mapTcbInPlace (Z : SystemState) (src : CSpaceAddr) (cap : Capability) :
    untypedDeriveRefused (Z.mapTcbInPlace x G) src cap = untypedDeriveRefused Z src cap := by
  unfold untypedDeriveRefused hasCdtChildren SystemState.linkHasChild
  simp only [getUntyped?_mapTcbInPlace_blind (G := G) x, slotLinkNodeWord_mapTcbInPlace_blind hG x]

include hG in
/-- **One capability's install commutes with the thread write.** -/
theorem ipcTransferSingleCap_mapTcbInPlace (cap : Capability) (src : SlotRef) (dst : CSpaceAddr)
    (Z : SystemState) (hNo : Z.objects.noResizeDue) :
    ipcTransferSingleCap cap src dst (Z.mapTcbInPlace x G) =
      mapStepState x G (ipcTransferSingleCap cap src dst Z) := by
  unfold ipcTransferSingleCap cdtNodeIsRevocable
  rw [getCNode?_mapTcbInPlace_blind (G := G) x, lookupSlotCap_mapTcbInPlace_blind (G := G) x,
    untypedDeriveRefused_mapTcbInPlace hG x, cspaceInsertSlot_mapTcbInPlace x _ _ _ hNo]
  cases Z.getCNode? dst.cnode with
  | none => rfl
  | some _ =>
    simp only []
    cases (SystemState.lookupSlotCap Z src).isSome with
    | false => rfl
    | true =>
      simp only []
      split
      · rfl
      · cases hI : cspaceInsertSlot dst cap.withoutMapping Z with
        | error e => rfl
        | ok p =>
          obtain ⟨⟨⟩, Zp⟩ := p
          have h1 := cspaceInsertSlot_noResizeDue _ _ _ _ hNo hI
          simp only [mapStepState]
          rw [cdtAddChild_mapTcbInPlace hG x _ _ _ _ h1,
            untypedSourceSetFull_mapTcbInPlace x _ _ _ (cdtAddChild_noResizeDue _ _ _ _ h1)]

theorem ipcTransferSingleCap_noResizeDue (cap : Capability) (src : SlotRef) (dst : CSpaceAddr)
    (Z Z' : SystemState) (hNo : Z.objects.noResizeDue)
    (h : ipcTransferSingleCap cap src dst Z = .ok ((), Z')) : Z'.objects.noResizeDue := by
  obtain ⟨_, Zq, -, -, -, hIns, rfl⟩ := ipcTransferSingleCap_ok_cases h
  exact untypedSourceSetFull_noResizeDue _ _ _
    (cdtAddChild_noResizeDue _ _ _ _ (cspaceInsertSlot_noResizeDue _ _ _ _ hNo hIns))

/-- The buffer word resolver reads only VSpace roots and the machine. -/
theorem ipcBufferWordPAddr?_mapTcbInPlace (Z : SystemState) (tcb : TCB) (idx : Nat)
    (w : Bool) :
    Architecture.IpcBufferRead.ipcBufferWordPAddr? (Z.mapTcbInPlace x G) tcb idx w =
      Architecture.IpcBufferRead.ipcBufferWordPAddr? Z tcb idx w := by
  unfold Architecture.IpcBufferRead.ipcBufferWordPAddr?
  rw [getVSpaceRoot?_mapTcbInPlace_blind (G := G) x]
  rfl

/-- A badge write commutes with the thread write. -/
theorem recordUnwrappedBadge_mapTcbInPlace (Z : SystemState) (rtcb : TCB) (i : Nat)
    (b : SeLe4n.Badge) :
    recordUnwrappedBadge (Z.mapTcbInPlace x G) rtcb i b =
      (recordUnwrappedBadge Z rtcb i b).mapTcbInPlace x G := by
  unfold recordUnwrappedBadge
  rw [ipcBufferWordPAddr?_mapTcbInPlace (G := G) x]
  split <;> rfl

end

end SeLe4n.Kernel
