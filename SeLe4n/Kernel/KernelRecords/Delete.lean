-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Finalise
import SeLe4n.Kernel.IPC.Invariant.DeleteReachability

/-!
# The deletes keep the records

WS-ZA ZA6.37.  A finalising delete is the slot's delete (a CNode and the
derivation tree), the teardown of the pages the destroyed capability recorded
(VSpace roots alone), and the retire of what it destroyed: the finalisation,
which is a `RecordsStep` (`RecordsStep.finaliseFinalObject`), and the erase,
which only removes objects.  The address-space records are carried by the
teardown's own theorem (`cspaceDeleteSlotFinalising_preserves_teardownWellFormed`),
the reply-waiter queues by the reachable bundle the delete carries
(`reachableDeleteBundle`), and no step writes a thread's fault fields but the
finalisation's, nor the machine's physical-address width.  The zombie delete
and the finalising revocation are chains of finalising deletes and
finalisations (`cspaceDeleteSlotZombie_closed`, `cspaceRevokeCdtFinalising_closed`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace FaultsStayParked

/-- A step after which every thread held a TCB it held before. -/
theorem of_tcb_back {st st' : SystemState}
    (h : ∀ (k : SeLe4n.ObjId) (t : TCB), st'.objects[k]? = some (.tcb t) →
      st.objects[k]? = some (.tcb t)) : FaultsStayParked st st' := fun u tcb' hT hF H =>
  H tcb' ((SystemState.getTcb?_eq_some_iff _ _ _).mpr
    (h _ _ ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT))) hF

/-- A write of VSpace roots alone. -/
theorem of_vspaceRootOnlyWrite {st st' : SystemState} (h : vspaceRootOnlyWrite st st') :
    FaultsStayParked st st' :=
  of_tcb_back fun k t hT => by
    rcases h k with e | ⟨-, r', hr'⟩
    · rw [← e]; exact hT
    · rw [hr'] at hT; cases hT

end FaultsStayParked

namespace RecordsFrame

/-- The slot's delete: the CNode, then the derivation tree. -/
theorem cspaceDeleteSlot {addr : CSpaceAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.cspaceDeleteSlot addr st = .ok ((), st')) : RecordsFrame st st' := by
  obtain ⟨stC, hC, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' h
  have F := cspaceDeleteSlotCore hInv hC
  have F2 := F.trans (withCdt stC (stC.cdt.spliceNode addr) F.invExt)
  exact F2.trans (of_linkReach (spliceDeletedCdtNode_reach stC addr) F2.invExt)

end RecordsFrame

/-- The interrupt node's retire writes the line's mask and the tree alone. -/
theorem retireIrqNode_physicalAddressWidth (st : SystemState) (x : SeLe4n.ObjId) :
    (retireIrqNode st x).machine.physicalAddressWidth = st.machine.physicalAddressWidth := by
  unfold retireIrqNode Architecture.setIrqLineSignal Architecture.setInterruptLineMask
    Architecture.recordPhysicalWrites
  simp only [MachineState.setIrqLineMask]

/-- **The retire keeps every fault record parked and the machine's width.** -/
theorem retireFinalisedObject_faults (ec : CoreId) (target recorder : Nat) (st : SystemState)
    (hInv : st.objects.invExt) :
    FaultsStayParked st (retireFinalisedObject ec target recorder st) ∧
      (retireFinalisedObject ec target recorder st).machine.physicalAddressWidth =
        st.machine.physicalAddressWidth := by
  rcases retireFinalisedObject_cases ec target recorder st with ⟨-, hE⟩ | ⟨-, hE⟩ <;> rw [hE]
  · exact ⟨FaultsStayParked.of_tcb_back fun k t hT => by rwa [retireIrqNode_objects] at hT,
      retireIrqNode_physicalAddressWidth _ _⟩
  · have F1 : RecordsFrame st (releaseFinalRegistration target st) :=
      releaseFinalRegistration_closed (RecordsFrame st)
        (fun _ _ _ F hR => F.trans (RecordsFrame.revokeService F.invExt hR)) target st
        (RecordsFrame.refl hInv)
    have S2 := (RecordsStep.of_frame F1).trans (RecordsStep.finaliseFinalObject target _ F1.invExt)
    refine ⟨S2.faults.trans (FaultsStayParked.of_tcb_back fun k t hT =>
      retireFinalObject_tcb_back ec target recorder _ S2.invExt hT), ?_⟩
    rw [(retireFinalObject_fields ec target recorder _).2.2]
    exact S2.width

/-- What a delete carries: the records, and the reachable bundle that carries
the reply-waiter queues. -/
def deleteRecordsCarried (s : SystemState) : Prop :=
  s.kernelRecordsSound ∧ reachableDeleteBundle s

/-- **The finalising delete keeps the records.** -/
theorem cspaceDeleteSlotFinalising_deleteRecordsCarried {ec : CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (hC : deleteRecordsCarried st)
    (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) : deleteRecordsCarried st' := by
  have hT := cspaceDeleteSlotFinalising_preserves_teardownWellFormed ec hC.1.1 h
  have hB := cspaceDeleteSlotFinalising_preserves_reachableDeleteBundle ec addr st st' hC.2 h
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st _ h
  have F1 := RecordsFrame.cspaceDeleteSlot (KernelRecords.objects_invExt hC.1) hD
  obtain ⟨hI2, hW2, -⟩ := finaliseDestroyedCapabilities_ok_frame ec _ _ st1 st2 F1.invExt hF
  have hM2 := (finaliseDestroyedCapabilities_framed ec _ _ st1 st2 hF).2
  have R := retireFinalisedObject_faults ec (slotRetireTarget st addr.cnode addr.slot)
    (slotRetireRecorder st addr.cnode addr.slot) st2 hI2
  refine ⟨⟨hT, hB.1.2.2.2.2.2.2, ?_, ?_⟩, hB⟩
  · exact ((FaultsStayParked.of_frame F1).trans
      ((FaultsStayParked.of_vspaceRootOnlyWrite hW2).trans R.1)).preserves hC.1.2.2.1
  · exact hC.1.2.2.2.of_eq (R.2.trans ((congrArg MachineState.physicalAddressWidth hM2).trans F1.width))

/-- The finalisation alone keeps the records. -/
theorem finaliseFinalObject_deleteRecordsCarried (target : Nat) {s : SystemState}
    (hC : deleteRecordsCarried s) : deleteRecordsCarried (finaliseFinalObject target s) := by
  have hB := finaliseFinalObject_preserves_reachableDeleteBundle target s hC.2
  exact ⟨(RecordsStep.finaliseFinalObject target s (KernelRecords.objects_invExt hC.1)).preserves
    (fun _ => hB.1.2.2.2.2.2.2) hC.1, hB⟩

/-- **The zombie delete keeps the records.** -/
theorem cspaceDeleteSlotZombie_deleteRecordsCarried {ec : CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (hC : deleteRecordsCarried st)
    (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) : deleteRecordsCarried st' :=
  cspaceDeleteSlotZombie_closed deleteRecordsCarried
    (fun _ _ _ hQ hD => cspaceDeleteSlotFinalising_deleteRecordsCarried hQ hD)
    (fun d _ hQ => finaliseFinalObject_deleteRecordsCarried d hQ) hC h

/-- **The finalising revocation keeps the records.** -/
theorem cspaceRevokeCdtFinalising_deleteRecordsCarried {ec : CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (hC : deleteRecordsCarried st)
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) : deleteRecordsCarried st' :=
  cspaceRevokeCdtFinalising_closed deleteRecordsCarried
    (fun _ _ _ hQ hD => cspaceDeleteSlotFinalising_deleteRecordsCarried hQ hD)
    (fun d _ hQ => finaliseFinalObject_deleteRecordsCarried d hQ) hC h

end SeLe4n.Kernel
