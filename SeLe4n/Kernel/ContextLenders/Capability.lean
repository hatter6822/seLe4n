-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.ReplyRecv

/-! # The capability and audit primitives write no reply object and no context

WS-SX SX8.  The primitive layer of the capability-only and audit arms, read for
the lenders: each step writes CNodes, thread records, endpoints, the derivation
tree, the service registry or the audit and ledger fields, and neither reply
objects nor scheduling contexts (`chainObjectsKept`), so it keeps every stack
(`LendersFrame.of_kept`, with the store's invariant read off the step's
`RecordsFrame`).  One lemma per `RecordsFrame` primitive the arms compose, at the
primitive layer only: the arm-level frames are derived once, by the dispatch's
case split.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace chainObjectsKept

theorem storeCNode {st st' : SystemState} {k : SeLe4n.ObjId} {cn' : CNode}
    (hInv : st.objects.invExt)
    (h : SeLe4n.Model.storeObject k (.cnode cn') st = .ok ((), st')) : chainObjectsKept st st' :=
  storeObject_other hInv h (fun _ e => by cases e) (fun _ e => by cases e)

theorem storeCNodeWith (st : SystemState) (k : SeLe4n.ObjId) (f : CNode → CNode)
    (hInv : st.objects.invExt) : chainObjectsKept st (st.storeCNodeWith k f) := by
  rcases SystemState.storeCNodeWith_cases st k f with ⟨_, _, hS⟩ | e
  · exact storeCNode hInv hS
  · rw [e]; exact refl _

theorem withCdt (st : SystemState) (c : CapDerivationTree) :
    chainObjectsKept st { st with cdt := c } := of_objects_eq rfl

/-- **Slot-link writes rewrite CNodes and threads alone.** -/
theorem of_linkReach {st₀ st : SystemState} (hR : SystemState.linkReach st₀ st)
    (hInv : st₀.objects.invExt) : chainObjectsKept st₀ st := by
  have key : ∀ (x : SeLe4n.ObjId) (o : KernelObject), st.objects[x]? = some o →
      (∀ cn, o ≠ .cnode cn) → (∀ t, o ≠ .tcb t) →
      st₀.objects[x]? = some o := fun x o hx hC hT => by
    rcases hR.agree hInv x with e | ⟨_, _, ha, hb, _⟩ | ⟨_, _, ha, hb, _⟩
    · first | (rw [← e]; exact hx) | (rw [e]; exact hx)
    all_goals first
      | (rw [ha] at hx; cases hx; first | exact absurd rfl (hC _) | exact absurd rfl (hT _))
      | (rw [hb] at hx; cases hx; first | exact absurd rfl (hC _) | exact absurd rfl (hT _))
  exact ⟨fun x r hx => key x _ hx (fun _ e => by cases e) (fun _ e => by cases e),
    fun x sc hx => key x _ hx (fun _ e => by cases e) (fun _ e => by cases e)⟩

theorem cdtAddChild (st : SystemState) (p c : SlotRef) (op : DerivationOp)
    (hInv : st.objects.invExt) : chainObjectsKept st (st.cdtAddChild p c op) :=
  (withCdt st _).trans (of_linkReach (SystemState.cdtAddChild_reach st p c op) hInv)

theorem cspaceInsertSlot {addr : CSpaceAddr} {cap : Capability} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.cspaceInsertSlot addr cap st = .ok ((), st')) :
    chainObjectsKept st st' := by
  obtain ⟨_, -, -, -, hS⟩ := cspaceInsertSlot_ok_decompose st st' addr cap h
  exact storeCNode hInv hS

theorem untypedSourceSetFull (st : SystemState) (src : CSpaceAddr) (cap : Capability)
    (hInv : st.objects.invExt) :
    chainObjectsKept st (_root_.SeLe4n.Kernel.untypedSourceSetFull st src cap) := by
  unfold _root_.SeLe4n.Kernel.untypedSourceSetFull _root_.SeLe4n.Kernel.setCapFreeIndex
  split
  · split
    · exact storeCNodeWith st _ _ hInv
    · exact refl _
  · exact refl _

theorem cspaceMint {src dst : CSpaceAddr} {rights : AccessRightSet} {badge : Option SeLe4n.Badge}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.cspaceMint src dst rights badge st = .ok ((), st')) :
    chainObjectsKept st st' := by
  unfold _root_.SeLe4n.Kernel.cspaceMint at hStep
  split at hStep
  · contradiction
  · rename_i parent stMid hLk
    have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
    subst hMid
    split at hStep
    · contradiction
    · split at hStep
      · contradiction
      · exact cspaceInsertSlot hInv hStep

theorem cspaceMintWithCdt {src dst : CSpaceAddr} {rights : AccessRightSet}
    {badge : Option SeLe4n.Badge} {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    chainObjectsKept st st' := by
  obtain ⟨_, stM, hMint, -, -, rfl⟩ := cspaceMintWithCdt_ok_decompose hStep
  have F := RecordsFrame.cspaceMint hInv hMint
  have F2 := RecordsFrame.cdtAddChild stM src dst .mint F.invExt
  exact ((cspaceMint hInv hMint).trans (cdtAddChild stM src dst .mint F.invExt)).trans
    (untypedSourceSetFull _ src _ F2.invExt)

theorem cspaceCopy {src dst : CSpaceAddr} {mask : AccessRightSet} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.cspaceCopy src dst mask st = .ok ((), st')) :
    chainObjectsKept st st' := by
  obtain ⟨_, st2, -, -, hIns, -, rfl⟩ := cspaceCopy_ok_decompose hStep
  have F := RecordsFrame.cspaceInsertSlot hInv hIns
  have F2 := RecordsFrame.cdtAddChild st2 src dst .copy F.invExt
  exact ((cspaceInsertSlot hInv hIns).trans (cdtAddChild st2 src dst .copy F.invExt)).trans
    (untypedSourceSetFull _ src _ F2.invExt)

/-- A slot cleared in a CNode or a thread's space slots. -/
theorem cspaceDeleteSlotCore {addr : CSpaceAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.cspaceDeleteSlotCore addr st = .ok ((), st')) :
    chainObjectsKept st st' := by
  obtain ⟨o, -, hH, hS⟩ := cspaceDeleteSlotCore_ok hStep
  refine storeObject_other hInv hS (fun r e => ?_) (fun sc e => ?_) <;>
    cases o <;> simp_all [KernelObject.removeSlotCap, KernelObject.holdsSlots]

theorem cspaceMove {src dst : CSpaceAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.cspaceMove src dst st = .ok ((), st')) :
    chainObjectsKept st st' := by
  unfold _root_.SeLe4n.Kernel.cspaceMove at hStep
  split at hStep
  · contradiction
  · split at hStep
    · contradiction
    · rename_i cap stMid hLk
      have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src cap hLk
      subst hMid
      split at hStep
      · contradiction
      · split at hStep
        · contradiction
        · rename_i st2 hIns
          have F := RecordsFrame.cspaceInsertSlot hInv hIns
          split at hStep
          · contradiction
          · rename_i st3 hDel
            have F3 := RecordsFrame.cspaceDeleteSlotCore F.invExt hDel
            cases hStep
            exact ((cspaceInsertSlot hInv hIns).trans (cspaceDeleteSlotCore F.invExt hDel)).trans
              ((withCdt st3 _).trans
                (of_linkReach (SystemState.cdtMove_reach st3 src dst) F3.invExt))

end chainObjectsKept

namespace LendersFrame

theorem cspaceMintWithCdt {src dst : CSpaceAddr} {rights : AccessRightSet}
    {badge : Option SeLe4n.Badge} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    LendersFrame st st' :=
  of_kept (chainObjectsKept.cspaceMintWithCdt hInv h) (RecordsFrame.cspaceMintWithCdt hInv h)

theorem cspaceCopy {src dst : CSpaceAddr} {mask : AccessRightSet} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.cspaceCopy src dst mask st = .ok ((), st')) : LendersFrame st st' :=
  of_kept (chainObjectsKept.cspaceCopy hInv h) (RecordsFrame.cspaceCopy hInv h)

theorem cspaceMove {src dst : CSpaceAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.cspaceMove src dst st = .ok ((), st')) : LendersFrame st st' :=
  of_kept (chainObjectsKept.cspaceMove hInv h) (RecordsFrame.cspaceMove hInv h)

/-- A service registration rewrites one endpoint. -/
theorem registerService {reg : ServiceRegistration} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.registerService reg st = .ok ((), st')) :
    LendersFrame st st' := by
  refine of_kept ?_ (RecordsFrame.registerService hInv h)
  obtain ⟨_, _, -, -, -, -, rfl⟩ := registerService_ok h
  exact chainObjectsKept.insert_other hInv (fun _ e => by cases e) (fun _ e => by cases e)

/-- The audit reads write nothing but their own trail. -/
theorem auditReadFromCore {ctx : GenericLabelingContext} {monitorClearance : Option SecurityDomain}
    {c : CoreId} {op : AuditReadOp} {st st' : SystemState} {w : Nat} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.auditReadFromCore ctx monitorClearance c op st = .ok (w, st')) :
    LendersFrame st st' := by
  rw [auditReadFromCore_frame _ _ _ _ _ _ _ h]; exact refl hInv

theorem auditDrainVisiblePrefix {ctx : GenericLabelingContext}
    {monitorClearance : Option SecurityDomain} {c : CoreId} {count n : Nat} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.auditDrainVisiblePrefix ctx monitorClearance c count st
      = .ok (n, st')) :
    LendersFrame st st' :=
  of_kept (by
      unfold _root_.SeLe4n.Kernel.auditDrainVisiblePrefix at h
      split at h
      · cases h; exact chainObjectsKept.of_objects_eq rfl
      · cases h)
    (RecordsFrame.auditDrainVisiblePrefix hInv h)

theorem declassifyObjectFromCore {ctx : GenericLabelingContext}
    {declPolicy : DeclassificationPolicy} {c : CoreId} {targetId : SeLe4n.ObjId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.declassifyObjectFromCore ctx declPolicy c targetId st
      = .ok ((), st')) :
    LendersFrame st st' := by
  refine of_kept ?_ (RecordsFrame.declassifyObjectFromCore hInv h)
  unfold _root_.SeLe4n.Kernel.declassifyObjectFromCore at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  rw [(authorizeDeclassificationOnCore_frame _ _ _ _ _ _ _ _ _ h).1]
  exact chainObjectsKept.of_objects_eq rfl

/-- Clearing a woken receiver's stash rewrites one thread's stash code. -/
theorem clearWokenReceiverStash (receiver? : Option SeLe4n.ThreadId) {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.clearWokenReceiverStash receiver? st = .ok ((), st')) :
    LendersFrame st st' := by
  refine of_kept ?_ (RecordsFrame.clearWokenReceiverStash receiver? hInv h)
  unfold _root_.SeLe4n.Kernel.clearWokenReceiverStash at h
  split at h
  · cases h; exact chainObjectsKept.refl _
  · split at h
    · split at h
      · exact chainObjectsKept.storeObject_other hInv h (fun _ e => by cases e)
          (fun _ e => by cases e)
      · cases h; exact chainObjectsKept.refl _
    · cases h; exact chainObjectsKept.refl _

theorem writeCallReturnWord (st : SystemState) (t : SeLe4n.ThreadId) (w : UInt64)
    (hInv : st.objects.invExt) : LendersFrame st (Architecture.writeCallReturnWord st t w) :=
  of_kept (Architecture.writeCallReturnWord_of_frame (chainObjectsKept st) (chainObjectsKept.refl _)
      (fun f => chainObjectsKept.writeReturnFrameToTcb st t f hInv))
    (RecordsFrame.writeCallReturnWord st t w hInv)

theorem stageWokenDelivery (st : SystemState) (w? : Option SeLe4n.ThreadId) (n : Nat)
    (hInv : st.objects.invExt) : LendersFrame st (Architecture.stageWokenDelivery st w? n) :=
  of_kept (chainObjectsKept.stageWokenDelivery st w? n hInv)
    (RecordsFrame.stageWokenDelivery st w? n hInv)

theorem stageDeliveredMessage (st : SystemState) (t : SeLe4n.ThreadId) (n : Nat)
    (hInv : st.objects.invExt) : LendersFrame st (Architecture.stageDeliveredMessage st t n) :=
  of_kept (chainObjectsKept.stageDeliveredMessage st t n hInv)
    (RecordsFrame.stageDeliveredMessage st t n hInv)

end LendersFrame

end SeLe4n.Kernel
