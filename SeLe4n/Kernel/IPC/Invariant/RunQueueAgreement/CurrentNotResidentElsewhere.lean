/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.YieldLinkedNotResident
import SeLe4n.Platform.Boot.InitialThreads

/-!
# A core's current thread is resident on no other core, across every entry

WS-ZA ZA6.10.  A remote deschedule empties a core's `current` slot while the
thread still runs there at EL0; until that core's next entry saves it, the
thread's live registers are in that core's bank (`MachineState.residentOnCore`),
not in its TCB.  A core that chose the thread then would resume a stale frame
while the first core still runs the live one.  seL4 never reaches the state:
`remoteTCBStall` holds the remote core's registers in the TCB, under the big
kernel lock, before another core can choose the thread.  This kernel holds the
thread off instead (`PriorityInheritance.deferResidentElsewhere`), and wakes the
deferring core once the first core's save releases it
(`PriorityInheritance.pokeReleasedResident`).

`SystemState.currentNotResidentElsewhere` states the property: a core's
non-idle current thread is resident on no other core, and no core holds an idle
thread's frame.  This file carries it across every committing entry, for every
pair of cores:

* the executing core's current thread: the deferral leaves it resident on no
  other core (`deferResidentElsewhere_current_not_elsewhere`), and the settle
  writes no other core's record;
* the executing core's resident thread: the settle records the thread the core
  resumes at EL0, which is its current thread, and no other core runs that
  thread (`currentDequeuedUnique`);
* every other pair: an entry makes no thread current on another core
  (`stepCovers.currentKept`) and makes no thread resident on one
  (`stepCovers.residentKept`).

So it holds at boot (no core holds a resident) and at every entry boundary
after.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-ZA ZA6.10: **a core's current thread is resident on no other core, and
no core holds an idle thread's frame.**  A thread whose live registers another
core's bank holds — the frame a remote deschedule left there until that core's
next entry saves it — is not resumed here (`deferResidentElsewhere`), and the
settle records only a thread the core resumes at EL0, never an idle one.  Idle
threads are left out of the first clause: each runs on its own core alone
(`currentDequeuedUniqueExcept.idleHome`). -/
structure _root_.SeLe4n.Model.SystemState.currentNotResidentElsewhere (st : SystemState) :
    Prop where
  elsewhere : ∀ (c d : CoreId) (tid : SeLe4n.ThreadId), c ≠ d →
    st.scheduler.currentOnCore c = some tid → isIdleThreadId tid = false →
    st.machine.residentOnCore d ≠ some tid
  residentNotIdle : ∀ (d : CoreId) (tid : SeLe4n.ThreadId),
    st.machine.residentOnCore d = some tid → isIdleThreadId tid = false

namespace CurrentNotResidentElsewhere

/-- A state no core holds a resident in satisfies it. -/
theorem of_noResidents {st : SystemState} (h : ∀ d, st.machine.residentOnCore d = none) :
    st.currentNotResidentElsewhere :=
  ⟨fun _ d _ _ _ _ hR => absurd (hR.symm.trans (h d)) (by simp),
   fun d _ hR => absurd (hR.symm.trans (h d)) (by simp)⟩

theorem default_residentCode :
    (default : SystemState).machine.residentCode = _root_.Vector.replicate _ 0 := rfl

/-- A machine whose residency codes are the default's holds no resident. -/
theorem of_defaultCodes {st : SystemState}
    (h : st.machine.residentCode = (default : SystemState).machine.residentCode) :
    st.currentNotResidentElsewhere :=
  of_noResidents fun d => by
    simp [MachineState.residentOnCore, h, default_residentCode,
      SeLe4n.PerCoreVector.get_eq_getElem]

/-- The property reads the current slots and the residency codes alone. -/
theorem of_frame {X Y : SystemState} (h : X.currentNotResidentElsewhere)
    (hS : Y.scheduler = X.scheduler) (hM : Y.machine.residentCode = X.machine.residentCode) :
    Y.currentNotResidentElsewhere := by
  have hR : ∀ d, Y.machine.residentOnCore d = X.machine.residentOnCore d := fun d => by
    simp only [MachineState.residentOnCore, hM]
  exact ⟨fun c d tid hcd hC hI => by rw [hR]; rw [hS] at hC; exact h.elsewhere c d tid hcd hC hI,
    fun d tid hD => h.residentNotIdle d tid (by rw [← hR]; exact hD)⟩

theorem clearLedgers' {X : SystemState} (h : X.currentNotResidentElsewhere) :
    (Architecture.clearPhysicalWrites
      (Architecture.clearIcacheMaintenance X)).currentNotResidentElsewhere :=
  of_frame h rfl rfl

end CurrentNotResidentElsewhere

/-- The default state holds no resident. -/
theorem _root_.SeLe4n.Model.SystemState.default_currentNotResidentElsewhere :
    (default : SystemState).currentNotResidentElsewhere :=
  CurrentNotResidentElsewhere.of_defaultCodes rfl

/-! ### The settle and the activation on the executing core -/

/-- No thread is current on two cores. -/
def currentsUnique (st : SystemState) : Prop :=
  ∀ c c' t, st.scheduler.currentOnCore c = some t → st.scheduler.currentOnCore c' = some t → c' = c

theorem currentsUnique_of_dequeuedUnique {st : SystemState} (h : st.currentDequeuedUnique) :
    currentsUnique st :=
  fun c c' t h1 h2 => (h.current c t h1).2.1 c' h2

theorem currentsUnique.of_scheduler {X Y : SystemState} (h : currentsUnique X)
    (hS : Y.scheduler = X.scheduler) : currentsUnique Y := by
  intro c c' t h1 h2; rw [hS] at h1 h2; exact h c c' t h1 h2

theorem currentsUnique.clearLedgers' {X : SystemState}
    (h : currentsUnique (Architecture.clearPhysicalWrites (Architecture.clearIcacheMaintenance X))) :
    currentsUnique X :=
  h.of_scheduler rfl

/-- A thread the deferral's check found resident nowhere else is resident on no
other core. -/
theorem residentOnCore_ne_of_residentElsewhere_false {st : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId} (h : PriorityInheritance.residentElsewhere st c tid = false)
    (d : CoreId) (hd : d ≠ c) : st.machine.residentOnCore d ≠ some tid := by
  intro hR
  unfold PriorityInheritance.residentElsewhere at h
  have := List.any_eq_false.mp h d (Concurrency.mem_allCores d)
  simp [hd, hR] at this

/-- **The settle and the activation on core `e` keep a core's current thread
resident on no other core**, after a step that wrote no other core's current
slot or residency record, into a state where no thread is current on two
cores. -/
theorem settleThenActivateOnCore_currentNotResidentElsewhere {e : CoreId} {pre M : SystemState}
    (hPre : pre.currentNotResidentElsewhere) (hInvM : M.objects.invExt)
    (hK : currentKeptOffCore e pre M) (hRK : residentKeptOffCore e pre M)
    (hU : currentsUnique (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e)) :
    (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e).currentNotResidentElsewhere := by
  have hCovS := settleResidencyOnCore_stepCovers e M hInvM
  have hInvD := dispatchVacatedCore_preserves_objects_invExt e M hInvM
  have hCovY := deferResidentElsewhere_stepCovers e _ hInvD
  have hPcur : ∀ c, (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e
      ).scheduler.currentOnCore c = (PriorityInheritance.deferResidentElsewhere
        (PriorityInheritance.dispatchVacatedCore M e) e).scheduler.currentOnCore c := fun c => by
    rw [activateThreadOnCore_scheduler, PriorityInheritance.settleResidencyOnCore_currentOnCore]
  have hPres : ∀ d, (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e
      ).machine.residentOnCore d =
        (PriorityInheritance.settleResidencyOnCore M e).machine.residentOnCore d :=
    fun d => activateThreadOnCore_residentOnCore _ e d
  -- The record on `e` is `e`'s current thread, which the core resumes at EL0.
  have hOwn : ∀ tid, (PriorityInheritance.settleResidencyOnCore M e).machine.residentOnCore e =
      some tid → (PriorityInheritance.deferResidentElsewhere
        (PriorityInheritance.dispatchVacatedCore M e) e).scheduler.currentOnCore e = some tid ∧
        isIdleThreadId tid = false := fun tid hR => by
    rw [PriorityInheritance.settleResidencyOnCore_resident] at hR
    split at hR
    · rename_i hT
      refine ⟨hR, ?_⟩
      cases hI : isIdleThreadId tid
      · rfl
      · rw [Architecture.restoreTargetOnCore_idle _ e tid hR hI] at hT; cases hT
    · cases hR
  refine ⟨fun c d tid hcd hC hI hR => ?_, fun d tid hR => ?_⟩
  · rw [hPres] at hR
    by_cases hc : c = e
    · subst hc
      have hd : d ≠ c := Ne.symm hcd
      rw [PriorityInheritance.settleResidencyOnCore_residentOnCore_ne M c d hcd] at hR
      have hD := hCovY.residentKept d hd tid hR
      rw [hPcur] at hC
      exact residentOnCore_ne_of_residentElsewhere_false
        (PriorityInheritance.deferResidentElsewhere_current_not_elsewhere _ c tid hC hI) d hd hD
    · by_cases hd : d = e
      · subst hd
        obtain ⟨hE, -⟩ := hOwn tid hR
        exact hc (hU d c tid (by rw [hPcur]; exact hE) hC)
      · rw [activateThreadOnCore_scheduler] at hC
        exact hPre.elsewhere c d tid hcd (hK c hc tid (hCovS.currentKept c hc tid hC)) hI
          (hRK d hd tid (hCovS.residentKept d hd tid hR))
  · rw [hPres] at hR
    by_cases hd : d = e
    · subst hd; exact (hOwn tid hR).2
    · exact hPre.residentNotIdle d tid (hRK d hd tid (hCovS.residentKept d hd tid hR))

/-- ...for a per-core entry's raw core id: on an id naming no core the entry
wrote no current slot and no residency record. -/
theorem settleThenActivateAt_currentNotResidentElsewhere {pre M : SystemState} {coreId : UInt64}
    (hPre : pre.currentNotResidentElsewhere) (hInvM : M.objects.invExt)
    (hK : ∀ c, Concurrency.coreIdOfUInt64? coreId = some c →
      currentKeptOffCore c pre M ∧ residentKeptOffCore c pre M)
    (hN : Concurrency.coreIdOfUInt64? coreId = none →
      M.scheduler = pre.scheduler ∧ M.machine.residentCode = pre.machine.residentCode)
    (hU : currentsUnique
      (activateThreadAt (PriorityInheritance.settleResidencyAt M coreId) coreId)) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt M coreId)
      coreId).currentNotResidentElsewhere := by
  unfold activateThreadAt PriorityInheritance.settleResidencyAt at hU ⊢
  cases hc : Concurrency.coreIdOfUInt64? coreId with
  | none => rw [hc] at hU; exact CurrentNotResidentElsewhere.of_frame hPre (hN hc).1 (hN hc).2
  | some c =>
    rw [hc] at hU
    exact settleThenActivateOnCore_currentNotResidentElsewhere hPre hInvM (hK c hc).1 (hK c hc).2 hU

/-! ### The trap-frame saves write no residency record -/

theorem saveCapturedTrapFrame_residentCode (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    (Architecture.saveCapturedTrapFrame st c frame).machine.residentCode =
      st.machine.residentCode := by
  cases frame with
  | none => rfl
  | some ic =>
    simp only [Architecture.saveCapturedTrapFrame, Architecture.saveVacatedFrameOnCore,
      Architecture.saveTrapFrameOnCore]
    (repeat' split) <;> simp [SystemState.updateTcb_machine]

theorem saveCapturedSyscallFrame_residentCode (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    (Architecture.saveCapturedSyscallFrame st c frame).machine.residentCode =
      st.machine.residentCode := by
  cases frame with
  | none => rfl
  | some ic =>
    simp only [Architecture.saveCapturedSyscallFrame, Architecture.saveVacatedFrameOnCore,
      Architecture.saveTrapFrameOnCore]
    (repeat' split) <;> simp [SystemState.updateTcb_machine]

theorem saveCapturedTrapFrameAt_residentCode (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    (Concurrency.saveCapturedTrapFrameAt st coreId frame).machine.residentCode =
      st.machine.residentCode := by
  unfold Concurrency.saveCapturedTrapFrameAt
  split
  · exact saveCapturedTrapFrame_residentCode st _ frame
  · rfl

theorem saveCapturedSyscallFrameAt_residentCode (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    (Concurrency.saveCapturedSyscallFrameAt st coreId frame).machine.residentCode =
      st.machine.residentCode := by
  unfold Concurrency.saveCapturedSyscallFrameAt
  split
  · exact saveCapturedSyscallFrame_residentCode st _ frame
  · rfl

/-- The frames an entry's save and step keep, off the executing core. -/
theorem keptOffCore_of_save_stepCovers {e : CoreId} {pre S M : SystemState}
    (hS : S.scheduler = pre.scheduler) (hM : S.machine.residentCode = pre.machine.residentCode)
    (h : stepCovers e S M) : currentKeptOffCore e pre M ∧ residentKeptOffCore e pre M :=
  ⟨currentKeptOffCore_trans (currentKeptOffCore_of_eq fun _ _ => by rw [hS]) h.currentKept,
   residentKeptOffCore_trans (residentKeptOffCore_of_eq hM) h.residentKept⟩

/-! ### Every committing entry -/

/-- **The timer entry keeps a core's current thread resident on no other
core.**  The tick reads its placement and coverage premises at the saved state,
as its stage does (`perCoreTimerTickEntryState_runQueueEntryStage`). -/
theorem perCoreTimerTickEntryState_preserves_currentNotResidentElsewhere (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hInv : (Concurrency.saveCapturedTrapFrameAt st coreId frame).objects.invExt)
    (hRef : (Concurrency.saveCapturedTrapFrameAt st coreId frame).releaseQueueRefined)
    (hD : (Concurrency.saveCapturedTrapFrameAt st coreId frame).currentDequeuedUnique)
    (hBi : schedContextBindingBidirectional (Concurrency.saveCapturedTrapFrameAt st coreId frame))
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) d)
    (hC : st.currentNotResidentElsewhere) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))
      ).currentNotResidentElsewhere := by
  have S := perCoreTimerTickEntryState_runQueueEntryStage coreId frame st hInv hRef hD hBi hAff
  have hU := currentsUnique_of_dequeuedUnique (S.2 hInv0 hR0 (S.1.links hInv0 hR0).2 hD0)
  have hSv := (saveCapturedTrapFrameAt_runQueueStage st coreId frame).1.links hInv0 hR0
  have hInvM := ((perCoreTimerTickStep_runQueueEntryStage _ coreId hInv hRef hD hBi hAff).1.links
    hInv hSv.2).1
  refine CurrentNotResidentElsewhere.of_frame
    (settleThenActivateAt_currentNotResidentElsewhere hC hInvM ?_ ?_ (hU.of_scheduler rfl)) rfl rfl
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    exact keptOffCore_of_save_stepCovers (saveCapturedTrapFrameAt_scheduler st coreId frame)
      (saveCapturedTrapFrameAt_residentCode st coreId frame)
      (perCoreTimerTickStep_stepCovers _ coreId h hInv hBi hD)
  · intro hc
    show (perCoreTimerTickStep _ coreId).1.scheduler = _ ∧
      (perCoreTimerTickStep _ coreId).1.machine.residentCode = _
    rw [perCoreTimerTickStep_invalid_core _ coreId (not_lt_of_coreIdOfUInt64?_none hc)]
    exact ⟨saveCapturedTrapFrameAt_scheduler st coreId frame,
      saveCapturedTrapFrameAt_residentCode st coreId frame⟩

/-- **The reschedule entry keeps a core's current thread resident on no other
core** (the secondary core's first entry is this one). -/
theorem perCoreRescheduleEntryState_preserves_currentNotResidentElsewhere (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hC : st.currentNotResidentElsewhere) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))
      ).currentNotResidentElsewhere := by
  have S := perCoreRescheduleEntryState_runQueueEntryStage coreId frame st
  have hU := currentsUnique_of_dequeuedUnique (S.2 hInv0 hR0 (S.1.links hInv0 hR0).2 hD0)
  have hSv := (saveCapturedTrapFrameAt_runQueueStage st coreId frame).1.links hInv0 hR0
  have hInvM := ((perCoreRescheduleStep_runQueueEntryStage _ coreId).1.links hSv.1 hSv.2).1
  refine CurrentNotResidentElsewhere.of_frame
    (settleThenActivateAt_currentNotResidentElsewhere hC hInvM ?_ ?_ (hU.of_scheduler rfl)) rfl rfl
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine keptOffCore_of_save_stepCovers (saveCapturedTrapFrameAt_scheduler st coreId frame)
      (saveCapturedTrapFrameAt_residentCode st coreId frame) ?_
    show stepCovers _ _ (perCoreRescheduleStep _ coreId)
    unfold perCoreRescheduleStep
    rw [dif_pos h]
    split
    · rename_i st' h'
      exact handleRescheduleSgiOnCore_stepCovers _ _ st' hSv.1 h'
    · exact stepCovers_refl _ _
  · intro hc
    show (perCoreRescheduleStep _ coreId).scheduler = _ ∧
      (perCoreRescheduleStep _ coreId).machine.residentCode = _
    rw [perCoreRescheduleStep_invalid_core _ coreId (not_lt_of_coreIdOfUInt64?_none hc)]
    exact ⟨saveCapturedTrapFrameAt_scheduler st coreId frame,
      saveCapturedTrapFrameAt_residentCode st coreId frame⟩

/-- **The fault entry keeps a core's current thread resident on no other
core.** -/
theorem faultEntryState_preserves_currentNotResidentElsewhere (lctx : LabelingContext)
    (coreId : UInt64) (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hC : st.currentNotResidentElsewhere) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx
        (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).currentNotResidentElsewhere := by
  have St := faultEntryState_runQueueEntryStage lctx coreId frame ectx w st E
  have hU := currentsUnique_of_dequeuedUnique (St.2 hInv0 hR0 (St.1.links hInv0 hR0).2 hD0)
  have hS := saveCapturedTrapFrameAt_runQueueStage st coreId (some frame)
  have hSv := hS.1.links hInv0 hR0
  have hInvM := ((faultEntryStep_runQueueEntryStage lctx _ ectx w coreId
    (E.of_ipcFrame hS (saveCapturedTrapFrameAt_ipcFrame st coreId _))).1.links hSv.1 hSv.2).1
  refine CurrentNotResidentElsewhere.of_frame
    (settleThenActivateAt_currentNotResidentElsewhere hC hInvM ?_ ?_ (hU.of_scheduler rfl)) rfl rfl
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine keptOffCore_of_save_stepCovers (saveCapturedTrapFrameAt_scheduler st coreId (some frame))
      (saveCapturedTrapFrameAt_residentCode st coreId (some frame)) ?_
    unfold faultEntryStep
    rw [dif_pos h]
    split
    · split
      · exact stepCovers_refl _ _
      · exact faultEntryDeliver_stepCovers lctx _ _ ectx w _ hSv.1
    · exact stepCovers_refl _ _
  · intro hc
    unfold faultEntryStep
    rw [dif_neg (not_lt_of_coreIdOfUInt64?_none hc)]
    exact ⟨saveCapturedTrapFrameAt_scheduler st coreId (some frame),
      saveCapturedTrapFrameAt_residentCode st coreId (some frame)⟩

/-- **The unknown-syscall entry keeps a core's current thread resident on no
other core.** -/
theorem unknownSyscallEntryState_preserves_currentNotResidentElsewhere (lctx : LabelingContext)
    (coreId : UInt64) (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hC : st.currentNotResidentElsewhere) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).currentNotResidentElsewhere := by
  have St := unknownSyscallEntryState_runQueueEntryStage lctx coreId frame ectx w st E
  have hU := currentsUnique_of_dequeuedUnique (St.2 hInv0 hR0 (St.1.links hInv0 hR0).2 hD0)
  have hS := saveCapturedSyscallFrameAt_runQueueStage st coreId (some frame)
  have hF : IpcFrame st (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) := by
    unfold Concurrency.saveCapturedSyscallFrameAt
    split
    · exact saveCapturedSyscallFrame_ipcFrame st _ _
    · exact IpcFrame.refl _
  have hSv := hS.1.links hInv0 hR0
  have hInvM := ((unknownSyscallEntryStep_runQueueEntryStage lctx _ ectx w coreId
    (E.of_ipcFrame hS hF)).1.links hSv.1 hSv.2).1
  refine CurrentNotResidentElsewhere.of_frame
    (settleThenActivateAt_currentNotResidentElsewhere hC hInvM ?_ ?_ (hU.of_scheduler rfl)) rfl rfl
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine keptOffCore_of_save_stepCovers
      (saveCapturedSyscallFrameAt_scheduler st coreId (some frame))
      (saveCapturedSyscallFrameAt_residentCode st coreId (some frame)) ?_
    unfold unknownSyscallEntryStep
    rw [dif_pos h]
    split
    · exact faultEntryDeliver_stepCovers lctx _ _ ectx w _ hSv.1
    · exact stepCovers_refl _ _
  · intro hc
    unfold unknownSyscallEntryStep
    rw [dif_neg (not_lt_of_coreIdOfUInt64?_none hc)]
    exact ⟨saveCapturedSyscallFrameAt_scheduler st coreId (some frame),
      saveCapturedSyscallFrameAt_residentCode st coreId (some frame)⟩

theorem fpAccessOnCore_residentCode (st : SystemState) (c : CoreId) (live : Option FpContext) :
    (Architecture.fpAccessOnCore st c live).2.machine.residentCode = st.machine.residentCode := by
  unfold Architecture.fpAccessOnCore
  (repeat' split) <;> simp [Architecture.setFpOwner, Architecture.writeFpContextToTcb,
    SystemState.updateTcb_machine]

/-- **The FP/SIMD entry keeps a core's current thread resident on no other
core.** -/
theorem fpAccessEntryState_preserves_currentNotResidentElsewhere (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hC : st.currentNotResidentElsewhere) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId)
        coreId).currentNotResidentElsewhere := by
  have St := fpAccessEntryState_runQueueEntryStage coreId frame live st
  have hU := currentsUnique_of_dequeuedUnique (St.2 hInv0 hR0 (St.1.links hInv0 hR0).2 hD0)
  have hSv := (saveCapturedTrapFrameAt_runQueueStage st coreId frame).1.links hInv0 hR0
  have hFp : ∀ c, (Architecture.fpAccessOnCore
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) c live).2.objects.invExt := fun c =>
    ((fpAccessOnCore_runQueueStage _ c live).1.links hSv.1 hSv.2).1
  have hInvM : (fpAccessEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame)
      coreId live).2.objects.invExt := by
    unfold fpAccessEntryStep
    split
    · exact hSv.1
    · exact dispatchVacatedCore_preserves_objects_invExt _ _ (hFp _)
  refine settleThenActivateAt_currentNotResidentElsewhere hC hInvM ?_ ?_ hU
  · intro c hc
    unfold fpAccessEntryStep
    rw [hc]
    exact keptOffCore_of_save_stepCovers
      (by rw [Architecture.fpAccessOnCore_scheduler, saveCapturedTrapFrameAt_scheduler])
      (by rw [fpAccessOnCore_residentCode, saveCapturedTrapFrameAt_residentCode])
      (dispatchVacatedCore_stepCovers c _ (hFp c))
  · intro hc
    unfold fpAccessEntryStep
    rw [hc]
    exact ⟨saveCapturedTrapFrameAt_scheduler st coreId frame,
      saveCapturedTrapFrameAt_residentCode st coreId frame⟩

theorem syncUserWords_residentCode (st : SystemState) (bytes : ByteArray) (n : Nat) :
    (Architecture.IpcBufferRead.syncUserWords st bytes n).machine.residentCode =
      st.machine.residentCode := by
  unfold Architecture.IpcBufferRead.syncUserWords; split <;> rfl

/-- **The syscall entry keeps a core's current thread resident on no other
core.**  The dispatch's coverage reads its premises at the state the dispatch
runs from — the saved state with the entry's IPC-buffer words handed to it — as
the seam's does (`syscallDispatchCrossCoreStep_stepCovers`). -/
theorem syscallDispatchEntryState_preserves_currentNotResidentElsewhere (ctx : LabelingContext)
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
    (hC : st.currentNotResidentElsewhere) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2
      ).currentNotResidentElsewhere := by
  have St := syscallDispatchEntryState_runQueueEntryStage ctx e syscallId trapped frame bytes n st E
  have hU := currentsUnique_of_dequeuedUnique (St.2 hInv0 hR0 (St.1.links hInv0 hR0).2 hD0)
  have hU' := hU.of_scheduler (Architecture.IpcBufferRead.syncUserWords_scheduler _ _ _).symm
  refine CurrentNotResidentElsewhere.of_frame ?_
    (Architecture.IpcBufferRead.syncUserWords_scheduler _ _ _) (syncUserWords_residentCode _ _ _)
  have hInv : (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n).objects.invExt := by
    rw [Architecture.IpcBufferRead.syncUserWords_objects]
    exact ((saveCapturedSyscallFrame_runQueueStage st e frame).1.links hInv0 hR0).1
  have hS0 : (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler = st.scheduler := by
    rw [Architecture.IpcBufferRead.syncUserWords_scheduler, saveCapturedSyscallFrame_scheduler]
  have hM0 : (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n).machine.residentCode =
        st.machine.residentCode := by
    rw [syncUserWords_residentCode, saveCapturedSyscallFrame_residentCode]
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
    trapped.pstate trapped.sp trapped.x30
    (Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame) bytes n)
  have hU'' : currentsUnique (syscallDispatchCrossCoreStep ctx e syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
    trapped.pstate trapped.sp trapped.x30
    (Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2 :=
    hU'
  show (syscallDispatchCrossCoreStep ctx e syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
    trapped.pstate trapped.sp trapped.x30
    (Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
      bytes n)).2.currentNotResidentElsewhere
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  obtain ⟨hDc, hDInv⟩ := syscallDispatchFromAbi_stepCovers hInv hB hPlaced hAwayCur hD
  obtain ⟨hStage, hStageInv⟩ := stageCallerReturnFor_stepCovers e
    ((Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
      bytes n).scheduler.currentOnCore e) st' outcome hDInv
  have hCov := stepCovers_trans (stepCovers_trans hDc hStage)
    (scheduleLocalSuccessorFrom_stepCovers e
      ((Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
        bytes n).scheduler.currentOnCore e) _ hStageInv)
  refine CurrentNotResidentElsewhere.clearLedgers'
    (settleThenActivateOnCore_currentNotResidentElsewhere hC
      (scheduleLocalSuccessorFrom_preserves_objects_invExt e _ _ hStageInv)
      (currentKeptOffCore_trans (currentKeptOffCore_of_eq fun _ _ => by rw [hS0]) hCov.currentKept)
      (residentKeptOffCore_trans (residentKeptOffCore_of_eq hM0) hCov.residentKept) ?_)
  rw [syscallDispatchCrossCoreStep_of_ok hD] at hU''
  exact currentsUnique.clearLedgers' hU''

end SeLe4n.Kernel

namespace SeLe4n.Platform.Boot
open SeLe4n.Model
open SeLe4n.Kernel

/-- WS-ZA ZA6.10: **the state the started boot installs keeps a core's current
thread resident on no other core** — no core holds a resident: no boot stage
writes a residency code (`bootFromPlatformCheckedWithIdleThreadsFor_ok_residentCode`,
`startInitialThreads_machine`, `linkBootCapabilities_machine`).  The first
entry's precondition for
`syscallDispatchEntryState_preserves_currentNotResidentElsewhere` and its
siblings. -/
theorem bootFromPlatformCheckedStartedFor_currentNotResidentElsewhere
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ist.state.currentNotResidentElsewhere := by
  obtain ⟨base, started, hBase, hStart, rfl⟩ := bootFromPlatformCheckedStartedFor_ok cores config ist h
  refine CurrentNotResidentElsewhere.of_defaultCodes ?_
  rw [linkBootCapabilities_machine, startInitialThreads_machine _ _ _ hStart]
  exact bootFromPlatformCheckedWithIdleThreadsFor_ok_residentCode cores config base hBase

end SeLe4n.Platform.Boot
