/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Entry

/-!
# No core's current or resident thread holds a yield link, across every entry

WS-ZA ZA6.8.  `completeYieldFrom`'s `setConsumed` writes a yielder's saved
register context, which is sound only while the saved context is the live one:
the yielder is no core's current thread (whose frame an entry has in flight)
and no core's resident thread (whose frame a remote deschedule left in that
core's bank).  `SystemState.yieldLinkedNotResident` states it; this file carries
it across every committing entry, for every core:

* the executing core: the entry's tail, the residency settle and the
  activation, leaves the core's current and resident threads unlinked
  (`activateThreadOnCore_current_unlinked`,
  `recordResidentThenActivate_runQueueEntryStage`);
* every other core: an entry makes no thread current there (the coverage
  relation's `currentKeptOffCore`), makes no linked thread resident anywhere
  and links no thread (the run-queue stage's `live` field,
  `YieldLinkLiveFrame`).

So it holds at boot (no code is set) and at every entry boundary after.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)
open SeLe4n.Kernel.Concurrency (CoreId)

/-! ### The composition -/

/-- Core `c`'s current thread, if any, holds no yield link. -/
def currentUnlinkedOn (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid t, st.scheduler.currentOnCore c = some tid → st.getTcb? tid = some t → t.yieldToCode = 0

/-- **Every current thread of the post-state was current on its core before, or
holds no yield link.** -/
def currentsRecordUnlinked (post pre : SystemState) : Prop :=
  ∀ c tid, post.scheduler.currentOnCore c = some tid →
    pre.scheduler.currentOnCore c = some tid ∨ ∀ t, post.getTcb? tid = some t → t.yieldToCode = 0

theorem currentsRecordUnlinked_of_scheduler_eq {pre post : SystemState}
    (h : post.scheduler = pre.scheduler) : currentsRecordUnlinked post pre :=
  fun _ _ hC => Or.inl (by rw [← h]; exact hC)

/-- A step on core `e` that keeps every other core's current thread and leaves
`e`'s unlinked. -/
theorem currentsRecordUnlinked_of_kept {e : CoreId} {pre post : SystemState}
    (hK : currentKeptOffCore e pre post) (hOwn : currentUnlinkedOn post e) :
    currentsRecordUnlinked post pre := fun c tid hC => by
  by_cases hc : c = e
  · rw [hc] at hC; exact Or.inr fun t hT => hOwn tid t hC hT
  · exact Or.inl (hK c hc tid hC)

/-- The record carries across a step writing neither the scheduler nor the
objects (a ledger drain, the IPC-buffer word clear). -/
theorem currentsRecordUnlinked.of_frame {pre X Y : SystemState}
    (h : currentsRecordUnlinked X pre) (hS : Y.scheduler = X.scheduler)
    (hO : Y.objects = X.objects) : currentsRecordUnlinked Y pre := fun c tid hC => by
  have hT : ∀ t, Y.getTcb? t = X.getTcb? t := fun t => by
    unfold SystemState.getTcb?; rw [hO]
  rw [hS] at hC
  rcases h c tid hC with e | e
  · exact Or.inl e
  · exact Or.inr fun t ht => e t (by rw [← hT]; exact ht)

/-- **The payoff's composition**: from a state with no linked thread current or
resident, a step that links no thread, makes no linked thread resident
(`YieldLinkLiveFrame`) and makes only unlinked threads current reaches one. -/
theorem yieldLinkedNotResident_of_live {pre post : SystemState}
    (hPre : pre.yieldLinkedNotResident) (hL : YieldLinkLiveFrame post pre)
    (hC : currentsRecordUnlinked post pre) : post.yieldLinkedNotResident := by
  intro d tid t hR hT
  have pre0 : (pre.scheduler.currentOnCore d = some tid ∨ pre.machine.residentOnCore d = some tid) →
      (objYieldCodes pre.objects[tid.toObjId]?).1 = 0 := fun h =>
    objYieldCodes_fst_zero_of_getTcb? fun t' hT' => hPre d tid t' h hT'
  have post0 : (objYieldCodes post.objects[tid.toObjId]?).1 = 0 → t.yieldToCode = 0 := fun h0 => by
    rw [objYieldCodes_of_getTcb? hT] at h0; exact h0
  rcases hR with h | h
  · rcases hC d tid h with h' | h'
    · exact post0 (hL.unset.zero (fun h => h) (pre0 (Or.inl h')))
    · exact h' t hT
  · rcases hL.residents d tid h with h' | h'
    · exact post0 (hL.unset.zero (fun h => h) (pre0 (Or.inr h')))
    · exact post0 h'

theorem currentsRecordUnlinked.clearLedgers {pre X : SystemState}
    (h : currentsRecordUnlinked X pre) : currentsRecordUnlinked
      (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites X)) pre :=
  h.of_frame rfl rfl

theorem currentsRecordUnlinked.clearLedgers' {pre X : SystemState}
    (h : currentsRecordUnlinked X pre) : currentsRecordUnlinked
      (Architecture.clearPhysicalWrites (Architecture.clearIcacheMaintenance X)) pre :=
  h.of_frame rfl rfl

theorem currentsRecordUnlinked.clearUserWords {pre X : SystemState}
    (h : currentsRecordUnlinked X pre) :
    currentsRecordUnlinked (Architecture.IpcBufferRead.clearUserWords X) pre :=
  h.of_frame (Architecture.IpcBufferRead.syncUserWords_scheduler _ _ _)
    (Architecture.IpcBufferRead.syncUserWords_objects _ _ _)

/-! ### The entry's tail on its own core -/

/-- After the activation, core `c`'s current thread holds no yield link. -/
theorem activateThreadOnCore_currentUnlinkedOn (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : currentUnlinkedOn (activateThreadOnCore st c) c :=
  activateThreadOnCore_current_unlinked st c hInv

/-- The activation on core `e` after a step keeping every other core's current
thread. -/
theorem activateThreadOnCore_currentsRecordUnlinked {e : CoreId} {pre M : SystemState}
    (hInvM : M.objects.invExt) (hK : currentKeptOffCore e pre M) :
    currentsRecordUnlinked (activateThreadOnCore M e) pre :=
  currentsRecordUnlinked_of_kept
    (currentKeptOffCore_trans hK
      (currentKeptOffCore_of_eq fun _ _ => by rw [activateThreadOnCore_scheduler]))
    (activateThreadOnCore_currentUnlinkedOn M e hInvM)

/-- The residency settle and the activation on core `e`. -/
theorem settleThenActivateOnCore_currentsRecordUnlinked {e : CoreId} {pre M : SystemState}
    (hInvM : M.objects.invExt) (hK : currentKeptOffCore e pre M) :
    currentsRecordUnlinked
      (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e) pre :=
  activateThreadOnCore_currentsRecordUnlinked (settleResidencyOnCore_preserves_objects_invExt e M hInvM)
    (currentKeptOffCore_trans hK (settleResidencyOnCore_stepCovers e M hInvM).currentKept)

/-- ...for a per-core entry's raw core id: on an id naming no core the entry
wrote no scheduler state. -/
theorem settleThenActivateAt_currentsRecordUnlinked {pre M : SystemState} {coreId : UInt64}
    (hInvM : M.objects.invExt)
    (hK : ∀ c, Concurrency.coreIdOfUInt64? coreId = some c → currentKeptOffCore c pre M)
    (hN : Concurrency.coreIdOfUInt64? coreId = none → M.scheduler = pre.scheduler) :
    currentsRecordUnlinked
      (activateThreadAt (PriorityInheritance.settleResidencyAt M coreId) coreId) pre := by
  unfold activateThreadAt PriorityInheritance.settleResidencyAt
  cases hc : Concurrency.coreIdOfUInt64? coreId with
  | none => exact currentsRecordUnlinked_of_scheduler_eq (hN hc)
  | some c => exact settleThenActivateOnCore_currentsRecordUnlinked hInvM (hK c hc)

theorem coreIdOfUInt64?_some {coreId : UInt64} {c : CoreId}
    (h : Concurrency.coreIdOfUInt64? coreId = some c) :
    ∃ hc : coreId.toNat < Concurrency.numCores, c = ⟨coreId.toNat, hc⟩ := by
  unfold Concurrency.coreIdOfUInt64? at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

theorem not_lt_of_coreIdOfUInt64?_none {coreId : UInt64}
    (h : Concurrency.coreIdOfUInt64? coreId = none) : ¬ coreId.toNat < Concurrency.numCores :=
  fun hc => by rw [Concurrency.coreIdOfUInt64?_eq_some coreId hc] at h; cases h

/-! ### The trap-frame saves write no scheduler state -/

theorem saveCapturedTrapFrame_scheduler (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    (Architecture.saveCapturedTrapFrame st c frame).scheduler = st.scheduler := by
  cases frame with
  | none => rfl
  | some ic =>
    simp only [Architecture.saveCapturedTrapFrame, Architecture.saveVacatedFrameOnCore_scheduler,
      Architecture.saveTrapFrameOnCore_scheduler]

theorem saveCapturedSyscallFrame_scheduler (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) :
    (Architecture.saveCapturedSyscallFrame st c frame).scheduler = st.scheduler := by
  cases frame with
  | none => rfl
  | some ic =>
    simp only [Architecture.saveCapturedSyscallFrame, Architecture.saveVacatedFrameOnCore_scheduler,
      Architecture.saveTrapFrameOnCore_scheduler]

theorem saveCapturedTrapFrameAt_scheduler (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    (Concurrency.saveCapturedTrapFrameAt st coreId frame).scheduler = st.scheduler := by
  unfold Concurrency.saveCapturedTrapFrameAt
  split
  · exact saveCapturedTrapFrame_scheduler st _ frame
  · rfl

theorem saveCapturedSyscallFrameAt_scheduler (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) :
    (Concurrency.saveCapturedSyscallFrameAt st coreId frame).scheduler = st.scheduler := by
  unfold Concurrency.saveCapturedSyscallFrameAt
  split
  · exact saveCapturedSyscallFrame_scheduler st _ frame
  · rfl

/-! ### Every committing entry -/

/-- **The timer entry keeps no linked thread current or resident.**  The tick
reads its placement and coverage premises at the saved state, as its stage
does (`perCoreTimerTickEntryState_runQueueEntryStage`). -/
theorem perCoreTimerTickEntryState_preserves_yieldLinkedNotResident (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined)
    (hInv : (Concurrency.saveCapturedTrapFrameAt st coreId frame).objects.invExt)
    (hRef : (Concurrency.saveCapturedTrapFrameAt st coreId frame).releaseQueueRefined)
    (hD : (Concurrency.saveCapturedTrapFrameAt st coreId frame).currentDequeuedUnique)
    (hBi : schedContextBindingBidirectional (Concurrency.saveCapturedTrapFrameAt st coreId frame))
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) d)
    (hY : st.yieldLinkedNotResident) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))).yieldLinkedNotResident := by
  have hSv := (saveCapturedTrapFrameAt_runQueueStage st coreId frame).1.links hInv0 hR0
  have hInvM := ((perCoreTimerTickStep_runQueueEntryStage _ coreId hInv hRef hD hBi hAff).1.links
    hInv hSv.2).1
  refine yieldLinkedNotResident_of_live hY
    ((perCoreTimerTickEntryState_runQueueEntryStage coreId frame st hInv hRef hD hBi hAff).1.live
      hInv0 hR0) ?_
  refine currentsRecordUnlinked.clearLedgers (settleThenActivateAt_currentsRecordUnlinked hInvM ?_ ?_)
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    exact currentKeptOffCore_trans
      (currentKeptOffCore_of_eq fun _ _ => by rw [saveCapturedTrapFrameAt_scheduler])
      (perCoreTimerTickStep_stepCovers _ coreId h hInv hBi hD).currentKept
  · intro hc
    show (perCoreTimerTickStep _ coreId).1.scheduler = _
    rw [perCoreTimerTickStep_invalid_core _ coreId (not_lt_of_coreIdOfUInt64?_none hc),
      saveCapturedTrapFrameAt_scheduler]

/-- **The reschedule entry keeps no linked thread current or resident** (the
secondary core's first entry is this one). -/
theorem perCoreRescheduleEntryState_preserves_yieldLinkedNotResident (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hY : st.yieldLinkedNotResident) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))).yieldLinkedNotResident := by
  have hSv := (saveCapturedTrapFrameAt_runQueueStage st coreId frame).1.links hInv0 hR0
  have hInvM := ((perCoreRescheduleStep_runQueueEntryStage _ coreId).1.links hSv.1 hSv.2).1
  refine yieldLinkedNotResident_of_live hY
    ((perCoreRescheduleEntryState_runQueueEntryStage coreId frame st).1.live hInv0 hR0) ?_
  refine currentsRecordUnlinked.clearLedgers (settleThenActivateAt_currentsRecordUnlinked hInvM ?_ ?_)
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine currentKeptOffCore_trans (b := Concurrency.saveCapturedTrapFrameAt st coreId frame)
      (currentKeptOffCore_of_eq fun _ _ => by rw [saveCapturedTrapFrameAt_scheduler]) ?_
    show currentKeptOffCore _ _ (perCoreRescheduleStep _ coreId)
    unfold perCoreRescheduleStep
    rw [dif_pos h]
    split
    · rename_i st' h'
      exact (handleRescheduleSgiOnCore_stepCovers _ _ st' hSv.1 h').currentKept
    · exact currentKeptOffCore_refl _ _
  · intro hc
    show (perCoreRescheduleStep _ coreId).scheduler = _
    rw [perCoreRescheduleStep_invalid_core _ coreId (not_lt_of_coreIdOfUInt64?_none hc),
      saveCapturedTrapFrameAt_scheduler]

/-- **The fault entry keeps no linked thread current or resident.** -/
theorem faultEntryState_preserves_yieldLinkedNotResident (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hY : st.yieldLinkedNotResident) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx
        (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).yieldLinkedNotResident := by
  have hS := saveCapturedTrapFrameAt_runQueueStage st coreId (some frame)
  have hSv := hS.1.links hInv0 hR0
  have hInvM := ((faultEntryStep_runQueueEntryStage lctx _ ectx w coreId
    (E.of_ipcFrame hS (saveCapturedTrapFrameAt_ipcFrame st coreId _))).1.links hSv.1 hSv.2).1
  refine yieldLinkedNotResident_of_live hY
    ((faultEntryState_runQueueEntryStage lctx coreId frame ectx w st E).1.live hInv0 hR0) ?_
  refine currentsRecordUnlinked.clearLedgers (settleThenActivateAt_currentsRecordUnlinked hInvM ?_ ?_)
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine currentKeptOffCore_trans (b := Concurrency.saveCapturedTrapFrameAt st coreId (some frame))
      (currentKeptOffCore_of_eq fun _ _ => by rw [saveCapturedTrapFrameAt_scheduler]) ?_
    unfold faultEntryStep
    rw [dif_pos h]
    split
    · split
      · exact currentKeptOffCore_refl _ _
      · exact (faultEntryDeliver_stepCovers lctx _ _ ectx w _ hSv.1).currentKept
    · exact currentKeptOffCore_refl _ _
  · intro hc
    unfold faultEntryStep
    rw [dif_neg (not_lt_of_coreIdOfUInt64?_none hc), saveCapturedTrapFrameAt_scheduler]

/-- **The unknown-syscall entry keeps no linked thread current or resident.** -/
theorem unknownSyscallEntryState_preserves_yieldLinkedNotResident (lctx : LabelingContext)
    (coreId : UInt64) (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hY : st.yieldLinkedNotResident) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).yieldLinkedNotResident := by
  have hS := saveCapturedSyscallFrameAt_runQueueStage st coreId (some frame)
  have hF : IpcFrame st (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) := by
    unfold Concurrency.saveCapturedSyscallFrameAt
    split
    · exact saveCapturedSyscallFrame_ipcFrame st _ _
    · exact IpcFrame.refl _
  have hSv := hS.1.links hInv0 hR0
  have hInvM := ((unknownSyscallEntryStep_runQueueEntryStage lctx _ ectx w coreId
    (E.of_ipcFrame hS hF)).1.links hSv.1 hSv.2).1
  refine yieldLinkedNotResident_of_live hY
    ((unknownSyscallEntryState_runQueueEntryStage lctx coreId frame ectx w st E).1.live hInv0 hR0) ?_
  refine currentsRecordUnlinked.clearLedgers (settleThenActivateAt_currentsRecordUnlinked hInvM ?_ ?_)
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine currentKeptOffCore_trans
      (b := Concurrency.saveCapturedSyscallFrameAt st coreId (some frame))
      (currentKeptOffCore_of_eq fun _ _ => by rw [saveCapturedSyscallFrameAt_scheduler]) ?_
    unfold unknownSyscallEntryStep
    rw [dif_pos h]
    split
    · exact (faultEntryDeliver_stepCovers lctx _ _ ectx w _ hSv.1).currentKept
    · exact currentKeptOffCore_refl _ _
  · intro hc
    unfold unknownSyscallEntryStep
    rw [dif_neg (not_lt_of_coreIdOfUInt64?_none hc), saveCapturedSyscallFrameAt_scheduler]

/-- **The FP/SIMD entry keeps no linked thread current or resident.** -/
theorem fpAccessEntryState_preserves_yieldLinkedNotResident (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hY : st.yieldLinkedNotResident) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId)
        coreId).yieldLinkedNotResident := by
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
  refine yieldLinkedNotResident_of_live hY
    ((fpAccessEntryState_runQueueEntryStage coreId frame live st).1.live hInv0 hR0)
    (settleThenActivateAt_currentsRecordUnlinked hInvM ?_ ?_)
  · intro c hc
    unfold fpAccessEntryStep
    rw [hc]
    exact currentKeptOffCore_trans
      (currentKeptOffCore_of_eq fun _ _ => by
        rw [Architecture.fpAccessOnCore_scheduler, saveCapturedTrapFrameAt_scheduler])
      (dispatchVacatedCore_stepCovers c _ (hFp c)).currentKept
  · intro hc
    unfold fpAccessEntryStep
    rw [hc, saveCapturedTrapFrameAt_scheduler]

/-- **The cross-core suspend keeps no linked thread current or resident**: it
runs on the executing core and activates the thread the core is left running. -/
theorem suspendThreadCrossCoreDrainedStep_preserves_yieldLinkedNotResident (tid : UInt64)
    (e : CoreId) (st : SystemState) (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined)
    (hY : st.yieldLinkedNotResident) :
    (suspendThreadCrossCoreDrainedStep tid e st).2.yieldLinkedNotResident := by
  refine yieldLinkedNotResident_of_live hY
    ((suspendThreadCrossCoreDrainedStep_runQueueEntryStage tid e st).1.live hInv0 hR0) ?_
  unfold suspendThreadCrossCoreDrainedStep suspendThreadCrossCoreStep
  dsimp only
  refine currentsRecordUnlinked.clearLedgers ?_
  split
  · exact currentsRecordUnlinked_of_scheduler_eq rfl
  · split
    · exact currentsRecordUnlinked_of_scheduler_eq rfl
    · unfold Concurrency.BracketSpec.run suspendThreadBracket
      dsimp only
      split
      · rename_i s' sgi hS
        obtain ⟨-, hSInv⟩ := suspendThreadOnCore_stepCovers st s' _ e sgi hInv0 hS
        exact currentsRecordUnlinked_of_kept (suspendThenScheduleLocal_stepCovers hInv0 hS).currentKept
          (activateThreadOnCore_currentUnlinkedOn _ e
            (scheduleLocalSuccessorFrom_preserves_objects_invExt e _ s' hSInv))
      · exact currentsRecordUnlinked_of_scheduler_eq rfl

/-- **The syscall entry keeps no linked thread current or resident.**  The
dispatch's coverage reads its premises at the state the dispatch runs from —
the saved state with the entry's IPC-buffer words handed to it — as the seam's
does (`syscallDispatchCrossCoreStep_stepCovers`). -/
theorem syscallDispatchEntryState_preserves_yieldLinkedNotResident (ctx : LabelingContext)
    (e : CoreId) (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (E : EntryPremises st)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined)
    (hB : finalisingDeleteBundle (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hPlaced : placedThreadsHaveTcbs (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hAwayCur : ∀ t, (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler.currentOnCore e = some t →
      ∀ c, (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n).queuedOn c t = false)
    (hY : st.yieldLinkedNotResident) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2).yieldLinkedNotResident := by
  refine yieldLinkedNotResident_of_live hY
    ((syscallDispatchEntryState_runQueueEntryStage ctx e syscallId trapped frame bytes n st E).1.live
      hInv0 hR0) (currentsRecordUnlinked.clearUserWords ?_)
  have hInv : (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n).objects.invExt := by
    rw [Architecture.IpcBufferRead.syncUserWords_objects]
    exact ((saveCapturedSyscallFrame_runQueueStage st e frame).1.links hInv0 hR0).1
  have hK0 : currentKeptOffCore e st (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n) :=
    currentKeptOffCore_of_eq fun _ _ => by
      rw [Architecture.IpcBufferRead.syncUserWords_scheduler, saveCapturedSyscallFrame_scheduler]
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
    trapped.pstate trapped.sp trapped.x30
    (Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame) bytes n)
  show currentsRecordUnlinked (syscallDispatchCrossCoreStep ctx e syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
    trapped.pstate trapped.sp trapped.x30
    (Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2 st
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  obtain ⟨-, hDInv⟩ := syscallDispatchFromAbi_stepCovers hInv hB hPlaced hAwayCur hD
  refine currentsRecordUnlinked.clearLedgers' (currentsRecordUnlinked_of_kept
    (currentKeptOffCore_trans hK0
      (syscallDispatchCrossCoreStep_stepCovers hInv hB hPlaced hAwayCur hD).currentKept)
    (activateThreadOnCore_currentUnlinkedOn _ e ?_))
  exact settleResidencyOnCore_preserves_objects_invExt e _
    (scheduleLocalSuccessorFrom_preserves_objects_invExt e _ _
      (stageCallerReturnFor_stepCovers e _ st' outcome hDInv).2)

end SeLe4n.Kernel
