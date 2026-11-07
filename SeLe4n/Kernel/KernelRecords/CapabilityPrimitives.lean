-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.IpcPrimitives

/-!
# The capability primitives keep every record view

WS-ZA ZA6.37.  A capability write stores a CNode over a CNode, writes the
derivation tree, or writes slot derivation links in CNodes and threads: none of
them is a thread's record view, a root, or the ASID table.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

namespace RecordsFrame

/-- A CNode stored over a CNode. -/
theorem storeCNode {st st' : SystemState} {k : SeLe4n.ObjId} {cn cn' : CNode}
    (hInv : st.objects.invExt) (hObj : st.objects[k]? = some (.cnode cn))
    (h : SeLe4n.Model.storeObject k (.cnode cn') st = .ok ((), st')) : RecordsFrame st st' :=
  storeObject hInv h (by rw [hObj]; rfl) (fun _ h => by cases h)

theorem storeCNodeWith (st : SystemState) (k : SeLe4n.ObjId) (f : CNode → CNode)
    (hInv : st.objects.invExt) : RecordsFrame st (st.storeCNodeWith k f) := by
  rcases SystemState.storeCNodeWith_cases st k f with ⟨cn, hO, hS⟩ | e
  · exact storeCNode hInv hO hS
  · rw [e]; exact refl hInv

/-- A write of the derivation tree alone. -/
theorem withCdt (st : SystemState) (c : CapDerivationTree) (hInv : st.objects.invExt) :
    RecordsFrame st { st with cdt := c } := of_objects_eq hInv rfl rfl

theorem erasure_links (o o' : KernelObject) (h : o.withoutLinks = o'.withoutLinks) :
    recordViewOf (some o) = recordViewOf (some o') := by
  cases o <;> cases o' <;>
    simp only [KernelObject.withoutLinks, reduceCtorEq, KernelObject.tcb.injEq,
      KernelObject.vspaceRoot.injEq, KernelObject.cnode.injEq] at h ⊢ <;>
    first | rfl | (subst h; rfl) | skip
  rename_i t t'
  show some (Sum.inl t.recordView) = some (Sum.inl t'.recordView)
  rw [TCB.proj_eq_of_withoutLinks_eq TCB.recordView h]

/-- **Slot-link writes keep every record view.** -/
theorem of_linkReach {st₀ st : SystemState} (hR : SystemState.linkReach st₀ st)
    (hInv : st₀.objects.invExt) : RecordsFrame st₀ st := by
  refine ⟨fun k => ?_, by rw [hR.fields], hR.invExt hInv, by rw [hR.fields]⟩
  rcases hR.agree hInv k with e | ⟨_, _, ha, hb, _⟩ | ⟨t, t', ha, hb, hw⟩
  · rw [e]
  · rw [ha, hb]; rfl
  · rw [ha, hb]
    show some (Sum.inl t'.recordView) = some (Sum.inl t.recordView)
    rw [TCB.proj_eq_of_withoutLinks_eq TCB.recordView hw]

theorem cdtAddChild (st : SystemState) (p c : SlotRef) (op : DerivationOp)
    (hInv : st.objects.invExt) : RecordsFrame st (st.cdtAddChild p c op) :=
  (withCdt st _ hInv).trans (of_linkReach (SystemState.cdtAddChild_reach st p c op) hInv)

theorem cspaceInsertSlot {addr : CSpaceAddr} {cap : Capability} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.cspaceInsertSlot addr cap st = .ok ((), st')) :
    RecordsFrame st st' := by
  obtain ⟨cn, hG, -, -, hS⟩ := cspaceInsertSlot_ok_decompose st st' addr cap h
  exact storeCNode hInv ((SystemState.getCNode?_eq_some_iff _ _ _).mp hG) hS

theorem setCapFreeIndex (st : SystemState) (addr : CSpaceAddr) (idx : Nat)
    (hInv : st.objects.invExt) : RecordsFrame st (_root_.SeLe4n.Kernel.setCapFreeIndex st addr idx) :=
  storeCNodeWith st addr.cnode _ hInv

theorem untypedSourceSetFull (st : SystemState) (src : CSpaceAddr) (cap : Capability)
    (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.untypedSourceSetFull st src cap) := by
  unfold _root_.SeLe4n.Kernel.untypedSourceSetFull
  split
  · split
    · exact setCapFreeIndex st src _ hInv
    · exact refl hInv
  · exact refl hInv

theorem ipcTransferSingleCap {cap : Capability} {srcNode : SlotRef}
    {receiverRoot : SeLe4n.ObjId} {slotBase : SeLe4n.Slot} {scanLimit : Nat}
    {st st' : SystemState} {result : CapTransferResult} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
      = .ok (result, st')) : RecordsFrame st st' := by
  obtain ⟨_, -, ⟨rfl, -⟩ | ⟨slot, st2, -, -, -, hIns, -, rfl⟩⟩ := ipcTransferSingleCap_ok_cases h
  · exact refl hInv
  · have F1 := cspaceInsertSlot hInv hIns
    have F2 := F1.trans (cdtAddChild st2 srcNode { cnode := receiverRoot, slot := slot }
      .ipcTransfer F1.invExt)
    exact F2.trans (untypedSourceSetFull _ srcNode cap F2.invExt)

theorem ipcUnwrapCapsLoop {caps : Array TransferCap} {receiverRoot : SeLe4n.ObjId}
    {idx : Nat} {nextBase : SeLe4n.Slot} {accResults : Array CapTransferResult} {fuel : Nat}
    {st st' : SystemState} {summary : CapTransferSummary} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.ipcUnwrapCapsLoop caps receiverRoot idx nextBase accResults fuel st
      = .ok (summary, st')) : RecordsFrame st st' := by
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    simp [_root_.SeLe4n.Kernel.ipcUnwrapCapsLoop] at h
    obtain ⟨_, rfl⟩ := h; exact refl hInv
  | succ n ih =>
    simp only [_root_.SeLe4n.Kernel.ipcUnwrapCapsLoop] at h
    cases hCap : caps[idx]? with
    | none => simp [hCap] at h; obtain ⟨_, rfl⟩ := h; exact refl hInv
    | some tc =>
      simp [hCap] at h
      cases hT : _root_.SeLe4n.Kernel.ipcTransferSingleCap tc.cap tc.srcSlot receiverRoot nextBase
          maxExtraCaps st with
      | error e => simp [hT] at h; obtain ⟨_, rfl⟩ := h; exact refl hInv
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have F1 := ipcTransferSingleCap hInv hT
        simp [hT] at h
        cases result <;> exact F1.trans (ih F1.invExt h)

theorem ipcUnwrapCaps {caps : Array TransferCap} {receiverRoot : SeLe4n.ObjId}
    {slotBase : SeLe4n.Slot} {grantRight : Bool} {st st' : SystemState}
    {summary : CapTransferSummary} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.ipcUnwrapCaps caps receiverRoot slotBase grantRight st
      = .ok (summary, st')) : RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.ipcUnwrapCaps at h
  split at h
  · simp at h; obtain ⟨_, rfl⟩ := h; exact refl hInv
  · exact ipcUnwrapCapsLoop hInv h

theorem receiveTransferCaps {req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)}
    {root : SeLe4n.ObjId} {base : SeLe4n.Slot} {st st' : SystemState}
    {summary : CapTransferSummary} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.receiveTransferCaps req root base st = .ok (summary, st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.receiveTransferCaps at h
  split at h
  · cases h; exact refl hInv
  · dsimp only at h
    split at h
    · cases h; exact refl hInv
    · exact ipcUnwrapCaps hInv h

end RecordsFrame

end SeLe4n.Kernel
