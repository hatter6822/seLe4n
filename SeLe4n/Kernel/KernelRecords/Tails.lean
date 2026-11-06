-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Scheduling
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.Architecture.IpcBufferRead
import SeLe4n.Kernel.Scheduler.ActivateThread

/-!
# What every entry does around its step keeps the records' reads

WS-ZA ZA6.37.  The saves of the trapped frame, the IPC-buffer words, the return
staging, the activation and the ledger clears write register files, the yield
link's codes, the machine and the ledgers: no record view reads them.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsFrame

theorem writeReturnFrameToTcb (st : SystemState) (t : SeLe4n.ThreadId)
    (f : Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    RecordsFrame st (Architecture.writeReturnFrameToTcb st t f) :=
  updateTcb st t hInv fun _ => rfl

theorem writeDeliveredFrameToTcb (st : SystemState) (t : SeLe4n.ThreadId)
    (f : Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    RecordsFrame st (Architecture.writeDeliveredFrameToTcb st t f) :=
  updateTcb st t hInv fun _ => rfl

theorem recordPhysicalWrites (st : SystemState) (ws : List Architecture.PhysicalWrite)
    (hInv : st.objects.invExt) : RecordsFrame st (_root_.SeLe4n.Kernel.Architecture.recordPhysicalWrites st ws) :=
  of_objects_eq hInv rfl rfl

theorem stageDeliveredMessage (st : SystemState) (t : SeLe4n.ThreadId) (n : Nat)
    (hInv : st.objects.invExt) : RecordsFrame st (Architecture.stageDeliveredMessage st t n) := by
  unfold Architecture.stageDeliveredMessage
  split
  · split
    · split
      · exact (writeDeliveredFrameToTcb st t _ hInv).trans
          (recordPhysicalWrites _ _ (writeDeliveredFrameToTcb st t _ hInv).invExt)
      · exact refl hInv
    · exact refl hInv
  · exact refl hInv

theorem stageWokenDelivery (st : SystemState) (w? : Option SeLe4n.ThreadId) (n : Nat)
    (hInv : st.objects.invExt) : RecordsFrame st (Architecture.stageWokenDelivery st w? n) := by
  unfold Architecture.stageWokenDelivery
  split
  · exact stageDeliveredMessage st _ n hInv
  · exact refl hInv

theorem stageWokenSendCompletion (st : SystemState) (w? : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (Architecture.stageWokenSendCompletion st w?) := by
  unfold Architecture.stageWokenSendCompletion
  repeat' split
  all_goals first
    | exact refl hInv
    | exact writeReturnFrameToTcb st _ _ hInv

theorem stageCallerReturnFor (caller? : Option SeLe4n.ThreadId) (st : SystemState) (c : CoreId)
    (o : Architecture.SyscallOutcome) (hInv : st.objects.invExt) :
    RecordsFrame st (Architecture.stageCallerReturnFor caller? st c o) := by
  cases o with
  | blocks => exact refl hInv
  | faulted => exact refl hInv
  | returns f =>
    cases caller? with
    | none => exact refl hInv
    | some tid =>
      simp only [Architecture.stageCallerReturnFor]
      have h := writeReturnFrameToTcb st tid f hInv
      split
      · exact h.trans (withMachine _ _ h.invExt)
      · exact h

theorem saveTrapFrameOnCore (st : SystemState) (c : CoreId) (rf : SeLe4n.RegisterFile)
    (hInv : st.objects.invExt) : RecordsFrame st (Architecture.saveTrapFrameOnCore st c rf) := by
  unfold Architecture.saveTrapFrameOnCore
  split
  · split
    · split
      · rename_i tid _ _ _ _
        have h := updateTcb st tid hInv (f := fun t => { t with registerContext := rf })
          fun _ => rfl
        exact h.trans (withMachine _ _ h.invExt)
      · exact refl hInv
    · exact refl hInv
  · exact refl hInv

theorem saveVacatedFrameOnCore (st : SystemState) (c : CoreId) (rf saved : SeLe4n.RegisterFile)
    (hInv : st.objects.invExt) :
    RecordsFrame st (Architecture.saveVacatedFrameOnCore st c rf saved) := by
  unfold Architecture.saveVacatedFrameOnCore
  split
  · split
    · split
      · exact updateTcb st _ hInv fun _ => rfl
      · exact refl hInv
    · exact refl hInv
  · exact refl hInv

theorem saveCapturedTrapFrame (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    RecordsFrame st (Architecture.saveCapturedTrapFrame st c frame) := by
  cases frame with
  | none => exact refl hInv
  | some ic =>
    have h := saveTrapFrameOnCore st c ic.snapshot hInv
    exact h.trans (saveVacatedFrameOnCore _ c _ _ h.invExt)

theorem saveCapturedSyscallFrame (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    RecordsFrame st (Architecture.saveCapturedSyscallFrame st c frame) := by
  cases frame with
  | none => exact refl hInv
  | some ic =>
    have h := saveTrapFrameOnCore st c ic.snapshot hInv
    exact h.trans (saveVacatedFrameOnCore _ c _ _ h.invExt)

theorem saveCapturedTrapFrameAt (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    RecordsFrame st (Concurrency.saveCapturedTrapFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedTrapFrameAt
  split
  · exact saveCapturedTrapFrame st _ frame hInv
  · exact refl hInv

theorem saveCapturedSyscallFrameAt (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    RecordsFrame st (Concurrency.saveCapturedSyscallFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedSyscallFrameAt
  split
  · exact saveCapturedSyscallFrame st _ frame hInv
  · exact refl hInv

theorem syncUserWords (st : SystemState) (bytes : ByteArray) (n : Nat)
    (hInv : st.objects.invExt) :
    RecordsFrame st (Architecture.IpcBufferRead.syncUserWords st bytes n) := by
  unfold Architecture.IpcBufferRead.syncUserWords
  split <;> exact withMachine _ _ hInv

theorem clearUserWords (st : SystemState) (hInv : st.objects.invExt) :
    RecordsFrame st (Architecture.IpcBufferRead.clearUserWords st) :=
  syncUserWords st _ _ hInv

theorem clearLedgers (st : SystemState) (hInv : st.objects.invExt) :
    RecordsFrame st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites st)) :=
  of_objects_eq hInv rfl rfl

theorem activateThreadOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (activateThreadOnCore st c) := by
  refine of_agreeOffYield (activateThreadOnCore_objectsAgreeOffYield st c hInv) ?_
    (activateThreadOnCore_preserves_objects_invExt st c hInv) ?_
  all_goals
    unfold _root_.SeLe4n.Kernel.activateThreadOnCore
    split
    · split
      · split
        · rfl
        · rename_i tid _ t _ k _
          unfold completeCurrentYield completeYieldTo cancelYieldTo setConsumed
          repeat' split
          all_goals first
            | records_width
            | simp only [SystemState.updateTcb_asidTable, SystemState.updateSchedContext_asidTable]
      · rfl
    · rfl

theorem activateThreadAt (st : SystemState) (coreId : UInt64) (hInv : st.objects.invExt) :
    RecordsFrame st (activateThreadAt st coreId) := by
  unfold _root_.SeLe4n.Kernel.activateThreadAt
  split
  · exact activateThreadOnCore st _ hInv
  · exact refl hInv

theorem settleResidencyAt (st : SystemState) (coreId : UInt64) (hInv : st.objects.invExt) :
    RecordsFrame st (PriorityInheritance.settleResidencyAt st coreId) := by
  unfold PriorityInheritance.settleResidencyAt
  split
  · exact settleResidencyOnCore st _ hInv
  · exact refl hInv

end RecordsFrame

end SeLe4n.Kernel
