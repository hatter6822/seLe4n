/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.BlockedNotResident

/-!
# Every core's resident thread has a TCB

WS-ZA ZA6.21.  A core's resident thread (`MachineState.residentOnCore`) is the
one whose live registers that core's bank holds; the core's next entry saves
them into the thread's TCB.  `blockedNotResident` (ZA6.16) reads a resident's
IPC state only when it has a TCB (`readyOrAbsent`), so on its own it would let a
resident's TCB be removed and a new one be retyped at the same id, blocked, with
the remote bank still waiting to be saved over it.  No step reaches that state —
every path that removes a TCB requires the thread held on no core: the final
retire's admission (`threadRetirable`, `threadHeldOnSomeCore`), the retype's
running-target rejection, and the carved erase, which removes no TCB — but no
theorem said so.  `SystemState.residentsHaveTcbs` states it, and this file
carries it from boot across every committing entry:

* a resident of another core was resident there before the entry
  (`stepCovers.residentKept`) and keeps its TCB (`stepCovers.residentTcbKept`,
  whose final-delete arm is `retireFinalObject_residentTcbKept`);
* the executing core's resident is the current thread its settle resumes at EL0
  (`settleThenActivateOnCore_residentCurrent`), which is active
  (`currentDequeuedUnique.currentActive`), so it has a TCB.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-ZA ZA6.21: **every core's resident thread has a TCB.** -/
def _root_.SeLe4n.Model.SystemState.residentsHaveTcbs (st : SystemState) : Prop :=
  ∀ (d : CoreId) (tid : SeLe4n.ThreadId),
    st.machine.residentOnCore d = some tid → (st.getTcb? tid).isSome

namespace ResidentsHaveTcbs

/-- A state no core holds a resident in satisfies it. -/
theorem of_noResidents {st : SystemState} (h : ∀ d, st.machine.residentOnCore d = none) :
    st.residentsHaveTcbs :=
  fun d _ hR => absurd (hR.symm.trans (h d)) (by simp)

/-- A machine whose residency codes are the default's holds no resident. -/
theorem of_defaultCodes {st : SystemState}
    (h : st.machine.residentCode = (default : SystemState).machine.residentCode) :
    st.residentsHaveTcbs :=
  of_noResidents fun d => by
    simp [MachineState.residentOnCore, h, CurrentNotResidentElsewhere.default_residentCode,
      SeLe4n.PerCoreVector.get_eq_getElem]

/-- **It carries across a step that keeps every residency record and every
TCB.** -/
theorem of_kept {X Y : SystemState} (h : X.residentsHaveTcbs)
    (hR : Y.machine.residentCode = X.machine.residentCode) (hT : tcbsKept X Y) :
    Y.residentsHaveTcbs := fun d tid hY => by
  have hX : X.machine.residentOnCore d = some tid := by
    simp only [MachineState.residentOnCore, hR] at hY ⊢; exact hY
  exact hT tid (h d tid hX)

/-- **The two halves at an entry's tail.**  A resident of another core was
resident there before (`hRK`) and keeps the TCB it had (`hTK`); `e`'s resident
is its current thread, which is active between scheduling points
(`currentDequeuedUnique`). -/
theorem of_tail {e : CoreId} {pre post : SystemState} (h : pre.residentsHaveTcbs)
    (hRK : residentKeptOffCore e pre post) (hTK : residentTcbKeptOffCore e pre post)
    (hOwn : ∀ tid, post.machine.residentOnCore e = some tid →
      post.scheduler.currentOnCore e = some tid)
    (hD : post.currentDequeuedUnique) : post.residentsHaveTcbs := fun d tid hR => by
  by_cases hd : d = e
  · subst hd
    obtain ⟨x, hx, -⟩ := hD.currentActive d tid (hOwn tid hR)
    rw [hx]; rfl
  · exact hTK d hd tid hR (h d tid (hRK d hd tid hR))

theorem clearLedgers {X : SystemState} (h : X.residentsHaveTcbs) :
    (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites X)).residentsHaveTcbs :=
  h

/-- ...and in the syscall step's order. -/
theorem clearLedgers' {X : SystemState} (h : X.residentsHaveTcbs) :
    (Architecture.clearPhysicalWrites
      (Architecture.clearIcacheMaintenance X)).residentsHaveTcbs :=
  h

end ResidentsHaveTcbs

/-! ### The settle and the activation on the executing core -/

/-- A step that writes TCBs only off their yield fields keeps every TCB a TCB. -/
theorem tcbsKept_of_objectsAgreeOffYield {st st' : SystemState}
    (h : SystemState.objectsAgreeOffYield st' st) : tcbsKept st st' := fun t hT => by
  have e := h.getTcb?_map (fun _ => ()) (fun _ => rfl) t
  rw [← Option.isSome_map (f := fun _ : TCB => ()), e, Option.isSome_map]
  exact hT

/-- **The settle and the activation keep every remote resident's TCB.** -/
theorem settleThenActivateOnCore_residentTcbKept (e : CoreId) (M : SystemState)
    (hInvM : M.objects.invExt) :
    residentKeptOffCore e M (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e) ∧
      residentTcbKeptOffCore e M
        (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e) := by
  have hCovS := settleResidencyOnCore_stepCovers e M hInvM
  have hInvS := settleResidencyOnCore_preserves_objects_invExt e M hInvM
  have hA : residentKeptOffCore e (PriorityInheritance.settleResidencyOnCore M e)
      (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e) :=
    fun d _ tid hR => by rw [activateThreadOnCore_residentOnCore] at hR; exact hR
  exact ⟨residentKeptOffCore_trans hCovS.residentKept hA,
    residentTcbKeptOffCore_trans hCovS.residentTcbKept
      (tcbsKept_of_objectsAgreeOffYield
        (activateThreadOnCore_objectsAgreeOffYield _ e hInvS)).residentTcbKept hA⟩

/-- **The settle and the activation on core `e` give every core's resident a
TCB**, after a step on `e` that recorded no new resident off `e` and kept each
remote resident's TCB, into a state between scheduling points. -/
theorem settleThenActivateOnCore_residentsHaveTcbs {e : CoreId} {pre M : SystemState}
    (h : pre.residentsHaveTcbs) (hInvM : M.objects.invExt)
    (hRK : residentKeptOffCore e pre M) (hTK : residentTcbKeptOffCore e pre M)
    (hD : (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e
      ).currentDequeuedUnique) :
    (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e).residentsHaveTcbs :=
  have S := settleThenActivateOnCore_residentTcbKept e M hInvM
  ResidentsHaveTcbs.of_tail h (residentKeptOffCore_trans hRK S.1)
    (residentTcbKeptOffCore_trans hTK S.2 S.1) (settleThenActivateOnCore_residentCurrent M e) hD

/-- ...for a per-core entry's raw core id: on an id naming no core the entry
recorded no resident and kept every TCB. -/
theorem settleThenActivateAt_residentsHaveTcbs {pre M : SystemState} {coreId : UInt64}
    (h : pre.residentsHaveTcbs) (hInvM : M.objects.invExt)
    (hK : ∀ c, Concurrency.coreIdOfUInt64? coreId = some c →
      residentKeptOffCore c pre M ∧ residentTcbKeptOffCore c pre M)
    (hN : Concurrency.coreIdOfUInt64? coreId = none →
      M.machine.residentCode = pre.machine.residentCode ∧ tcbsKept pre M)
    (hD : (activateThreadAt (PriorityInheritance.settleResidencyAt M coreId) coreId
      ).currentDequeuedUnique) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt M coreId) coreId).residentsHaveTcbs := by
  unfold activateThreadAt PriorityInheritance.settleResidencyAt at hD ⊢
  cases hc : Concurrency.coreIdOfUInt64? coreId with
  | none => exact ResidentsHaveTcbs.of_kept h (hN hc).1 (hN hc).2
  | some c =>
    rw [hc] at hD
    exact settleThenActivateOnCore_residentsHaveTcbs h hInvM (hK c hc).1 (hK c hc).2 hD

/-! ### The trap-frame saves and the FP/SIMD switch keep every TCB -/

theorem tcbsKept_saveTrapFrameOnCore (st : SystemState) (c : CoreId) (rf : SeLe4n.RegisterFile)
    (hInv : st.objects.invExt) : tcbsKept st (Architecture.saveTrapFrameOnCore st c rf) := by
  rcases Architecture.saveTrapFrameOnCore_frame st c rf with h | ⟨tid, -, -, -, -, h⟩
  · rw [h]; exact tcbsKept.refl st
  · rw [h]; exact tcbsKept.updateTcb st tid _ hInv

theorem tcbsKept_saveVacatedFrameOnCore (st : SystemState) (c : CoreId)
    (rf saved : SeLe4n.RegisterFile) (hInv : st.objects.invExt) :
    tcbsKept st (Architecture.saveVacatedFrameOnCore st c rf saved) := by
  unfold Architecture.saveVacatedFrameOnCore
  split
  · split
    · split
      · exact tcbsKept.updateTcb st _ _ hInv
      · exact tcbsKept.refl st
    · exact tcbsKept.refl st
  · exact tcbsKept.refl st

theorem tcbsKept_saveCapturedTrapFrameAt (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    tcbsKept st (Concurrency.saveCapturedTrapFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedTrapFrameAt
  split
  · cases frame with
    | none => exact tcbsKept.refl st
    | some ic =>
      exact (tcbsKept_saveTrapFrameOnCore st _ _ hInv).trans
        (tcbsKept_saveVacatedFrameOnCore _ _ _ _
          (Architecture.saveTrapFrameOnCore_preserves_objects_invExt st _ _ hInv))
  · exact tcbsKept.refl st

theorem tcbsKept_saveCapturedSyscallFrame (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    tcbsKept st (Architecture.saveCapturedSyscallFrame st c frame) := by
  cases frame with
  | none => exact tcbsKept.refl st
  | some ic =>
    exact (tcbsKept_saveTrapFrameOnCore st _ _ hInv).trans
      (tcbsKept_saveVacatedFrameOnCore _ _ _ _
        (Architecture.saveTrapFrameOnCore_preserves_objects_invExt st _ _ hInv))

theorem tcbsKept_saveCapturedSyscallFrameAt (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    tcbsKept st (Concurrency.saveCapturedSyscallFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedSyscallFrameAt
  split
  · exact tcbsKept_saveCapturedSyscallFrame st _ frame hInv
  · exact tcbsKept.refl st

theorem tcbsKept_fpAccessOnCore (st : SystemState) (c : CoreId) (live : Option FpContext)
    (hInv : st.objects.invExt) : tcbsKept st (Architecture.fpAccessOnCore st c live).2 := by
  unfold Architecture.fpAccessOnCore
  (repeat' split) <;> first
    | exact tcbsKept.refl st
    | exact tcbsKept.updateTcb st _ _ hInv

/-- The residency records and TCBs an entry's save and step keep, off the
executing core. -/
theorem residentTcbKeptOffCore_of_save_stepCovers {e : CoreId} {pre S M : SystemState}
    (hM : S.machine.residentCode = pre.machine.residentCode) (hT : tcbsKept pre S)
    (h : stepCovers e S M) : residentKeptOffCore e pre M ∧ residentTcbKeptOffCore e pre M :=
  ⟨residentKeptOffCore_trans (residentKeptOffCore_of_eq hM) h.residentKept,
   residentTcbKeptOffCore_trans hT.residentTcbKept h.residentTcbKept h.residentKept⟩

/-! ### Every committing entry -/

/-- **The timer entry gives every core's resident a TCB.** -/
theorem perCoreTimerTickEntryState_preserves_residentsHaveTcbs (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hInv : (Concurrency.saveCapturedTrapFrameAt st coreId frame).objects.invExt)
    (hRef : (Concurrency.saveCapturedTrapFrameAt st coreId frame).releaseQueueRefined)
    (hD : (Concurrency.saveCapturedTrapFrameAt st coreId frame).currentDequeuedUnique)
    (hBi : schedContextBindingBidirectional (Concurrency.saveCapturedTrapFrameAt st coreId frame))
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) d)
    (hT : st.residentsHaveTcbs) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))
      ).residentsHaveTcbs := by
  have S := perCoreTimerTickEntryState_runQueueEntryStage coreId frame st hInv hRef hD hBi hAff
  have hDf := S.2 hInv0 hR0 (S.1.links hInv0 hR0).2 hD0
  obtain ⟨hInvS, hRS⟩ := (saveCapturedTrapFrameAt_runQueueStage st coreId frame).1.links hInv0 hR0
  have hInvM :=
    ((perCoreTimerTickStep_runQueueEntryStage _ coreId hInv hRef hD hBi hAff).1.links hInvS hRS).1
  have hSv := tcbsKept_saveCapturedTrapFrameAt st coreId frame hInv0
  refine ResidentsHaveTcbs.clearLedgers
    (settleThenActivateAt_residentsHaveTcbs hT hInvM ?_ ?_
      (currentDequeuedUnique_of_clearLedgers hDf))
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    exact residentTcbKeptOffCore_of_save_stepCovers
      (saveCapturedTrapFrameAt_residentCode st coreId frame) hSv
      (perCoreTimerTickStep_stepCovers _ coreId h hInv hBi hD)
  · intro hc
    show (perCoreTimerTickStep _ coreId).1.machine.residentCode = _ ∧
      tcbsKept _ (perCoreTimerTickStep _ coreId).1
    rw [perCoreTimerTickStep_invalid_core _ coreId (not_lt_of_coreIdOfUInt64?_none hc)]
    exact ⟨saveCapturedTrapFrameAt_residentCode st coreId frame, hSv⟩

/-- **The reschedule entry gives every core's resident a TCB** (the secondary
core's first entry is this one). -/
theorem perCoreRescheduleEntryState_preserves_residentsHaveTcbs (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hT : st.residentsHaveTcbs) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))
      ).residentsHaveTcbs := by
  have S := perCoreRescheduleEntryState_runQueueEntryStage coreId frame st
  have hDf := S.2 hInv0 hR0 (S.1.links hInv0 hR0).2 hD0
  obtain ⟨hInvS, hRS⟩ := (saveCapturedTrapFrameAt_runQueueStage st coreId frame).1.links hInv0 hR0
  have hInvM := ((perCoreRescheduleStep_runQueueEntryStage _ coreId).1.links hInvS hRS).1
  have hSv := tcbsKept_saveCapturedTrapFrameAt st coreId frame hInv0
  refine ResidentsHaveTcbs.clearLedgers
    (settleThenActivateAt_residentsHaveTcbs hT hInvM ?_ ?_
      (currentDequeuedUnique_of_clearLedgers hDf))
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine residentTcbKeptOffCore_of_save_stepCovers
      (saveCapturedTrapFrameAt_residentCode st coreId frame) hSv ?_
    show stepCovers _ _ (perCoreRescheduleStep _ coreId)
    unfold perCoreRescheduleStep
    rw [dif_pos h]
    split
    · rename_i st' h'
      exact handleRescheduleSgiOnCore_stepCovers _ _ st' hInvS h'
    · exact stepCovers_refl _ _
  · intro hc
    show (perCoreRescheduleStep _ coreId).machine.residentCode = _ ∧
      tcbsKept _ (perCoreRescheduleStep _ coreId)
    rw [perCoreRescheduleStep_invalid_core _ coreId (not_lt_of_coreIdOfUInt64?_none hc)]
    exact ⟨saveCapturedTrapFrameAt_residentCode st coreId frame, hSv⟩

/-- **The fault entry gives every core's resident a TCB.** -/
theorem faultEntryState_preserves_residentsHaveTcbs (lctx : LabelingContext)
    (coreId : UInt64) (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hT : st.residentsHaveTcbs) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx
        (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).residentsHaveTcbs := by
  have St := faultEntryState_runQueueEntryStage lctx coreId frame ectx w st E
  have hDf := St.2 hInv0 hR0 (St.1.links hInv0 hR0).2 hD0
  have hS := saveCapturedTrapFrameAt_runQueueStage st coreId (some frame)
  obtain ⟨hInvS, hRS⟩ := hS.1.links hInv0 hR0
  have hInvM := ((faultEntryStep_runQueueEntryStage lctx _ ectx w coreId
    (E.of_ipcFrame hS (saveCapturedTrapFrameAt_ipcFrame st coreId _))).1.links hInvS hRS).1
  have hSv := tcbsKept_saveCapturedTrapFrameAt st coreId (some frame) hInv0
  refine ResidentsHaveTcbs.clearLedgers
    (settleThenActivateAt_residentsHaveTcbs hT hInvM ?_ ?_
      (currentDequeuedUnique_of_clearLedgers hDf))
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine residentTcbKeptOffCore_of_save_stepCovers
      (saveCapturedTrapFrameAt_residentCode st coreId (some frame)) hSv ?_
    unfold faultEntryStep
    rw [dif_pos h]
    split
    · split
      · exact stepCovers_refl _ _
      · exact faultEntryDeliver_stepCovers lctx _ _ ectx w _ hInvS
    · exact stepCovers_refl _ _
  · intro hc
    unfold faultEntryStep
    rw [dif_neg (not_lt_of_coreIdOfUInt64?_none hc)]
    exact ⟨saveCapturedTrapFrameAt_residentCode st coreId (some frame), hSv⟩

/-- **The unknown-syscall entry gives every core's resident a TCB.** -/
theorem unknownSyscallEntryState_preserves_residentsHaveTcbs (lctx : LabelingContext)
    (coreId : UInt64) (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hT : st.residentsHaveTcbs) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).residentsHaveTcbs := by
  have St := unknownSyscallEntryState_runQueueEntryStage lctx coreId frame ectx w st E
  have hDf := St.2 hInv0 hR0 (St.1.links hInv0 hR0).2 hD0
  have hS := saveCapturedSyscallFrameAt_runQueueStage st coreId (some frame)
  have hF : IpcFrame st (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) := by
    unfold Concurrency.saveCapturedSyscallFrameAt
    split
    · exact saveCapturedSyscallFrame_ipcFrame st _ _
    · exact IpcFrame.refl _
  obtain ⟨hInvS, hRS⟩ := hS.1.links hInv0 hR0
  have hInvM := ((unknownSyscallEntryStep_runQueueEntryStage lctx _ ectx w coreId
    (E.of_ipcFrame hS hF)).1.links hInvS hRS).1
  have hSv := tcbsKept_saveCapturedSyscallFrameAt st coreId (some frame) hInv0
  refine ResidentsHaveTcbs.clearLedgers
    (settleThenActivateAt_residentsHaveTcbs hT hInvM ?_ ?_
      (currentDequeuedUnique_of_clearLedgers hDf))
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine residentTcbKeptOffCore_of_save_stepCovers
      (saveCapturedSyscallFrameAt_residentCode st coreId (some frame)) hSv ?_
    unfold unknownSyscallEntryStep
    rw [dif_pos h]
    split
    · exact faultEntryDeliver_stepCovers lctx _ _ ectx w _ hInvS
    · exact stepCovers_refl _ _
  · intro hc
    unfold unknownSyscallEntryStep
    rw [dif_neg (not_lt_of_coreIdOfUInt64?_none hc)]
    exact ⟨saveCapturedSyscallFrameAt_residentCode st coreId (some frame), hSv⟩

/-- **The FP/SIMD entry gives every core's resident a TCB.** -/
theorem fpAccessEntryState_preserves_residentsHaveTcbs (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hT : st.residentsHaveTcbs) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId)
        coreId).residentsHaveTcbs := by
  have St := fpAccessEntryState_runQueueEntryStage coreId frame live st
  have hD := St.2 hInv0 hR0 (St.1.links hInv0 hR0).2 hD0
  obtain ⟨hInvS, hRS⟩ := (saveCapturedTrapFrameAt_runQueueStage st coreId frame).1.links hInv0 hR0
  have hSv := tcbsKept_saveCapturedTrapFrameAt st coreId frame hInv0
  have hFp : ∀ c, (Architecture.fpAccessOnCore
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) c live).2.objects.invExt := fun c =>
    ((fpAccessOnCore_runQueueStage _ c live).1.links hInvS hRS).1
  have hInvM : (fpAccessEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame)
      coreId live).2.objects.invExt := by
    unfold fpAccessEntryStep
    split
    · exact hInvS
    · exact dispatchVacatedCore_preserves_objects_invExt _ _ (hFp _)
  refine settleThenActivateAt_residentsHaveTcbs hT hInvM ?_ ?_ hD
  · intro c hc
    unfold fpAccessEntryStep
    rw [hc]
    exact residentTcbKeptOffCore_of_save_stepCovers
      (by rw [fpAccessOnCore_residentCode, saveCapturedTrapFrameAt_residentCode])
      (hSv.trans (tcbsKept_fpAccessOnCore _ c live hInvS))
      (dispatchVacatedCore_stepCovers c _ (hFp c))
  · intro hc
    unfold fpAccessEntryStep
    rw [hc]
    exact ⟨saveCapturedTrapFrameAt_residentCode st coreId frame, hSv⟩

/-- **The syscall entry gives every core's resident a TCB.**  The dispatch's
coverage reads its premises at the state the dispatch runs from — the saved
state with the entry's IPC-buffer words handed to it — as the seam's does
(`syscallDispatchCrossCoreStep_stepCovers`). -/
theorem syscallDispatchEntryState_preserves_residentsHaveTcbs (ctx : LabelingContext)
    (e : CoreId) (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (E : EntryPremises st)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hB : finalisingDeleteBundle (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hPlaced : placedThreadsHaveTcbs (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hAwayCur : ∀ t, (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler.currentOnCore e = some t →
      ∀ c, (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n).queuedOn c t = false)
    (hT : st.residentsHaveTcbs) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2
      ).residentsHaveTcbs := by
  refine ResidentsHaveTcbs.of_kept (X := (syscallDispatchCrossCoreStep ctx e syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
    trapped.pstate trapped.sp trapped.x30
    (Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
      bytes n)).2) ?_ (syncUserWords_residentCode _ ByteArray.empty 0)
    (tcbsKept.of_objects_eq (Architecture.IpcBufferRead.syncUserWords_objects _ ByteArray.empty 0))
  have hS := (saveCapturedSyscallFrame_runQueueStage st e frame).trans
    (SystemState.RunQueueStage.of_frame (Architecture.IpcBufferRead.syncUserWords_objects _ _ _)
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (hT := by unfold Architecture.IpcBufferRead.syncUserWords; split <;> rfl)
      (hS := by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (hRes := by unfold Architecture.IpcBufferRead.syncUserWords; split <;> rfl)
      (st' := Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
  have hF := (saveCapturedSyscallFrame_ipcFrame st e frame).trans
    (IpcFrame.of_frame (Architecture.IpcBufferRead.syncUserWords_objects
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n)
      fun _ => by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
  have ES := E.of_ipcFrame hS hF
  obtain ⟨hInvS, hRS⟩ := hS.1.links hInv0 hR0
  have hM0 : (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n).machine.residentCode =
        st.machine.residentCode := by
    rw [syncUserWords_residentCode, saveCapturedSyscallFrame_residentCode]
  have hT0 : tcbsKept st (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n) :=
    (tcbsKept_saveCapturedSyscallFrame st e frame hInv0).trans
      (tcbsKept.of_objects_eq (Architecture.IpcBufferRead.syncUserWords_objects _ _ _))
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
    trapped.pstate trapped.sp trapped.x30
    (Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame) bytes n)
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  have A := syscallDispatchFromAbi_runQueueEntryStage ES hD
  have B := (stageCallerReturnFor_runQueueStage ((Architecture.IpcBufferRead.syncUserWords
    (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler.currentOnCore e)
    st' e outcome)
  have ABC := A.trans (B.entry.trans (scheduleLocalSuccessorFrom_runQueueEntryStage
    ((Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
      bytes n).scheduler.currentOnCore e) _ e))
  have Full := hS.entry.trans (ABC.trans (settleThenActivateOnCore_runQueueEntryStage _ e))
  have hInvM := (ABC.1.links hInvS hRS).1
  obtain ⟨hDc, hDInv⟩ := syscallDispatchFromAbi_stepCovers hInvS hB hPlaced hAwayCur hD
  obtain ⟨hStage, hStageInv⟩ := stageCallerReturnFor_stepCovers e
    ((Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
      bytes n).scheduler.currentOnCore e) st' outcome hDInv
  have hCov := stepCovers_trans (stepCovers_trans hDc hStage)
    (scheduleLocalSuccessorFrom_stepCovers e
      ((Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
        bytes n).scheduler.currentOnCore e) _ hStageInv)
  have K := residentTcbKeptOffCore_of_save_stepCovers hM0 hT0 hCov
  exact ResidentsHaveTcbs.clearLedgers'
    (settleThenActivateOnCore_residentsHaveTcbs hT hInvM K.1 K.2
      (Full.2 hInv0 hR0 (Full.1.links hInv0 hR0).2 hD0))

end SeLe4n.Kernel

namespace SeLe4n.Platform.Boot
open SeLe4n.Model
open SeLe4n.Kernel

/-- WS-ZA ZA6.21: **the state the started boot installs gives every core's
resident a TCB** — no core holds a resident: no boot stage writes a residency
code.  The first entry's precondition for
`syscallDispatchEntryState_preserves_residentsHaveTcbs` and its siblings. -/
theorem bootFromPlatformCheckedStartedFor_residentsHaveTcbs
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ist.state.residentsHaveTcbs := by
  obtain ⟨base, started, hBase, hStart, rfl⟩ := bootFromPlatformCheckedStartedFor_ok cores config ist h
  refine ResidentsHaveTcbs.of_defaultCodes ?_
  rw [linkBootCapabilities_machine, startInitialThreads_machine _ _ _ hStart]
  exact bootFromPlatformCheckedWithIdleThreadsFor_ok_residentCode cores config base hBase

end SeLe4n.Platform.Boot
