-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.VSpace

/-!
# The thread-space set and the handler arms keep the records

WS-ZA ZA6.37.  A thread's space slot set is the slot copied — a space slot and
the derivation tree, a `RecordsFrame` — then the object its old capability was
the last capability to retired: the retire keeps the teardown's
well-formedness by its own theorem (`retireFinalObject_preserves_teardownWellFormed`),
writes no thread's fault fields and not the machine, and the reply-waiter
queues are carried by the reachable state the set keeps
(`threadSlotSet_preserves_ipcReachable`).  The space change through the zombie
delete is a run of finalising deletes (`deleteRecordsCarried`) and then the
plain space change; the handler bind and clear are a zombie delete and a copy.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

namespace RecordsFrame

/-- **The slot copy** of a thread's space slot: the slot cleared, the tree
spliced, then, when the source holds a capability, the slot written and its
derivation edge. -/
theorem threadSlotCopied {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    RecordsFrame st (_root_.SeLe4n.Kernel.threadSlotCopied st tid slot srcCNode srcSlot rights) := by
  have hPre := (SystemState.getTcb?_eq_some_iff st tid t).mp hT
  have F1 := storeObject hInv (threadSlotCleared_store hT slot) (by rw [hPre]; rfl) (fun _ => by simp)
  have F2 := F1.trans (withCdt _ ((threadSlotCleared tid.toObjId slot st).cdt.spliceNode
    { cnode := tid.toObjId, slot := slot }) F1.invExt)
  have F3 := F2.trans (of_linkReach (spliceDeletedCdtNode_reach _ _) F2.invExt)
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨-, e⟩ | ⟨cap, -, e⟩
  · rw [e]; exact F3
  · rw [e]
    have F4 := F3.trans (updateTcb _ tid F3.invExt (fun _ => rfl)
      (f := (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights))))
    exact F4.trans (cdtAddChild _ _ _ _ F4.invExt)

end RecordsFrame

/-- **The retire of a final object carries the records** once the reply-waiter
queues are carried: it keeps the teardown's well-formedness, leaves no thread
that was not one before, and writes no machine state. -/
theorem retireFinalObject_kernelRecordsSound (ec : Concurrency.CoreId) (target recorder : Nat)
    {s : SystemState} (h : s.kernelRecordsSound)
    (hRW : (retireFinalObject ec target recorder s).replyWaitersConsistent) :
    (retireFinalObject ec target recorder s).kernelRecordsSound :=
  ⟨(retireFinalObject_preserves_teardownWellFormed ec target recorder s h.1).1, hRW,
    (FaultsStayParked.of_tcb_back fun _ _ hT => retireFinalObject_tcb_back ec target recorder s
      (KernelRecords.objects_invExt h) hT).preserves h.2.2.1,
    h.2.2.2.of_eq (by rw [(retireFinalObject_fields ec target recorder s).2.2])⟩

/-- **A thread space slot's set carries the records**, the reachable state
carrying the reply-waiter queues. -/
theorem threadSlotSet_kernelRecordsSound (ec : Concurrency.CoreId) {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (h : st.kernelRecordsSound) (hR : ipcReachable st)
    (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId)
    (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    (threadSlotSet ec st tid slot srcCNode srcSlot rights).kernelRecordsSound := by
  have hR' := threadSlotSet_preserves_ipcReachable ec hR hT slot srcCNode srcSlot rights
  unfold threadSlotSet at hR' ⊢
  exact retireFinalObject_kernelRecordsSound ec _ _
    ((RecordsFrame.threadSlotCopied (KernelRecords.objects_invExt h) hT slot srcCNode srcSlot
      rights).preserves h) hR'.2.2.2.2.2.2

/-- **The space change carries the records**: each slot set does. -/
theorem copyThreadSpaces_kernelRecordsSound (ec : Concurrency.CoreId) {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr} (h : st.kernelRecordsSound)
    (hR : ipcReachable st) (hStep : copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st') :
    st'.kernelRecordsSound := by
  obtain ⟨tcb, hT, -, -, hCn, -, rfl⟩ := copyThreadSpaces_ok hStep
  obtain ⟨cnCap, -, hCL, -⟩ := cspaceRootSourceAdmitted_spec hCn
  obtain ⟨t1, hT1'⟩ := Option.isSome_iff_exists.mp
    (threadSlotSet_getTcb? ec hR.objects_invExt hT (slot := TCB.cspaceRootSlot) (by decide)
      cnSrc.cnode cnSrc.slot TCB.cspaceRootRights hCL)
  exact threadSlotSet_kernelRecordsSound ec (threadSlotSet_kernelRecordsSound ec h hR hT _ _ _ _)
    (threadSlotSet_preserves_ipcReachable ec hR hT _ _ _ _) hT1' _ _ _ _

/-- **The space change through the zombie delete carries the records**: the
loop's passes carry them with the bundle the deletes read, and the space change
after them. -/
theorem copyThreadSpacesZombie_kernelRecordsSound (ec : Concurrency.CoreId) {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr} (h : deleteRecordsCarried st)
    (hStep : copyThreadSpacesZombie ec st vtid cnSrc vrSrc = .ok st') : st'.kernelRecordsSound := by
  have hChain : ∀ n s, ZombieRun ec n st s → deleteRecordsCarried s := fun _ _ hR =>
    hR.chain.closed deleteRecordsCarried
      (fun _ _ _ hQ hD => cspaceDeleteSlotFinalising_deleteRecordsCarried hQ hD)
      (fun d _ hQ => finaliseFinalObject_deleteRecordsCarried d hQ) h
  rcases copyThreadSpacesZombie_cases hStep with h1 | ⟨n, s, hR, rfl | h2⟩
  · exact copyThreadSpaces_kernelRecordsSound ec h.1 h.2.1 h1
  · exact (hChain n _ hR).1
  · exact copyThreadSpaces_kernelRecordsSound ec (hChain n s hR).1 (hChain n s hR).2.1 h2

/-- **The handler bind carries the records**: the node slot's zombie delete,
then the copy of a notification capability. -/
theorem irqHandlerSetNotification_kernelRecordsSound {ec : Concurrency.CoreId} {line : Nat}
    {src : CSpaceAddr} {st st' : SystemState} (h : deleteRecordsCarried st)
    (hStep : irqHandlerSetNotification ec line src st = .ok ((), st')) : st'.kernelRecordsSound := by
  obtain ⟨-, st1, -, -, -, hZ, hC⟩ :=
    irqHandlerSetNotification_ok (KernelRecords.objects_invExt h.1) hStep
  have h1 := cspaceDeleteSlotZombie_deleteRecordsCarried h hZ
  exact (RecordsFrame.cspaceCopy (KernelRecords.objects_invExt h1.1) hC).preserves h1.1

/-- **The handler clear carries the records**: the node slot's zombie delete. -/
theorem irqHandlerClear_kernelRecordsSound {ec : Concurrency.CoreId} {line : Nat}
    {st st' : SystemState} (h : deleteRecordsCarried st)
    (hStep : irqHandlerClear ec line st = .ok ((), st')) : st'.kernelRecordsSound := by
  unfold irqHandlerClear at hStep
  split at hStep
  · cases hStep
  exact (cspaceDeleteSlotZombie_deleteRecordsCarried h hStep).1

end SeLe4n.Kernel
