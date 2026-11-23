-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Stage
import SeLe4n.Kernel.FaultEntry
import SeLe4n.Kernel.PerCoreRescheduleEntry

/-! # The entries that lend nothing keep the lenders' flow

WS-SX SX8.  The reschedule interrupt and the FP/SIMD access write thread
records, the scheduler and the machine, and no reply object or context, so
each is a lenders' stage outright; the only premise is the store's invariant at
the state the entry runs from, which the intermediate frames read
(`LendersPremises.invExt`).  The entries that can lend or link a caller (the
syscall, the interrupt's bound signal, the fault delivery) take the full
`LendersPremises` there. -/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace chainObjectsKept

theorem perCoreRescheduleStep (st : SystemState) (coreId : UInt64) (hInv : st.objects.invExt) :
    chainObjectsKept st (_root_.SeLe4n.Kernel.perCoreRescheduleStep st coreId) := by
  unfold _root_.SeLe4n.Kernel.perCoreRescheduleStep
  split
  · split
    · rename_i hR; exact handleRescheduleSgiOnCore hInv hR
    · exact refl _
  · exact refl _

theorem fpAccessOnCore (st : SystemState) (c : CoreId) (live : Option FpContext)
    (hInv : st.objects.invExt) : chainObjectsKept st (Architecture.fpAccessOnCore st c live).2 := by
  have hSet : ∀ (s : SystemState) (t? : Option SeLe4n.ThreadId), chainObjectsKept st s →
      chainObjectsKept st (Architecture.setFpOwner s c t?) := fun s _ F =>
    F.trans (of_objects_eq rfl)
  unfold Architecture.fpAccessOnCore
  split
  · exact refl _
  · split
    · exact refl _
    · split
      · exact refl _
      · split
        · exact refl _
        · dsimp only
          apply hSet
          split
          · unfold Architecture.writeFpContextToTcb
            exact updateTcb _ _ _ hInv
          · exact refl _

end chainObjectsKept

/-- The FP/SIMD switch keeps the store's invariant: a thread record's write. -/
theorem fpAccessOnCore_invExt (st : SystemState) (c : CoreId) (live : Option FpContext)
    (hInv : st.objects.invExt) : (Architecture.fpAccessOnCore st c live).2.objects.invExt := by
  have hSet : ∀ (s : SystemState) (t? : Option SeLe4n.ThreadId), s.objects.invExt →
      (Architecture.setFpOwner s c t?).objects.invExt := fun _ _ h => h
  unfold Architecture.fpAccessOnCore
  split
  · exact hInv
  · split
    · exact hInv
    · split
      · exact hInv
      · split
        · exact hInv
        · dsimp only
          apply hSet
          split
          · unfold Architecture.writeFpContextToTcb
            exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv
          · exact hInv

/-- **The reschedule entry's committed state keeps the lenders' flow.** -/
theorem perCoreRescheduleEntryState_lendersStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (hInv : st.objects.invExt) :
    LendersStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) := by
  have F1 := RecordsFrame.saveCapturedTrapFrameAt st coreId frame hInv
  have F2 : (_root_.SeLe4n.Kernel.perCoreRescheduleStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId).objects.invExt := by
    unfold _root_.SeLe4n.Kernel.perCoreRescheduleStep
    split
    · split
      · rename_i hR; exact (RecordsFrame.handleRescheduleSgiOnCore F1.invExt hR).invExt
      · exact F1.invExt
    · exact F1.invExt
  exact ((LendersStage.of_kept (chainObjectsKept.saveCapturedTrapFrameAt st coreId frame hInv)).trans
    (LendersStage.of_kept (chainObjectsKept.perCoreRescheduleStep _ coreId F1.invExt))).trans
    (LendersStage.entryTail _ coreId F2)

/-- **The FP/SIMD entry's committed state keeps the lenders' flow.** -/
theorem fpAccessEntryState_lendersStage (ctx : LabelingContext) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext)
    (st : SystemState) (hInv : st.objects.invExt) :
    LendersStage ctx st (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId) coreId) := by
  have F1 := RecordsFrame.saveCapturedTrapFrameAt st coreId frame hInv
  refine (LendersStage.of_kept (chainObjectsKept.saveCapturedTrapFrameAt st coreId frame hInv)).trans ?_
  have hStep : chainObjectsKept (Concurrency.saveCapturedTrapFrameAt st coreId frame)
      (fpAccessEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 ∧
      (fpAccessEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2.objects.invExt := by
    unfold fpAccessEntryStep
    split
    · exact ⟨chainObjectsKept.refl _, F1.invExt⟩
    · rename_i c _
      have G := fpAccessOnCore_invExt _ c live F1.invExt
      exact ⟨(chainObjectsKept.fpAccessOnCore _ c live F1.invExt).trans
          (chainObjectsKept.dispatchVacatedCore _ c G),
        (RecordsFrame.dispatchVacatedCore _ c G).invExt⟩
  refine (LendersStage.of_kept hStep.1).trans ?_
  exact (LendersStage.of_kept (chainObjectsKept.settleResidencyAt _ coreId hStep.2)).trans
    (LendersStage.activateThreadAt _ coreId (RecordsFrame.settleResidencyAt _ coreId hStep.2).invExt)

end SeLe4n.Kernel
