/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.CurrentNotResidentElsewhere
import SeLe4n.Kernel.Architecture.TrapFrameSaveInvariant

/-!
# The executing core's bank is its current thread's context after the settle

WS-ZA ZA6.10.  The residency settle (`PriorityInheritance.settleResidencyOnCore`)
can now switch the executing core to its idle thread, when its chosen thread is
still resident on another core, and raise another core's reschedule flag.  This
module proves the settle keeps `contextMatchesCurrentOnCore` on the executing
core — the switch establishes the match, the vacating fallback leaves no
current thread, and the record and the poke touch neither the bank nor the
store — and composes it with the save, the step and the activation into the
entry-level theorems for the timer and reschedule entries.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)
open SeLe4n.Kernel.PriorityInheritance

/-- The vacated core's dispatch keeps the core's match. -/
theorem dispatchVacatedCore_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (dispatchVacatedCore st c) c := by
  unfold dispatchVacatedCore
  split
  · exact h
  · split
    · rename_i st' hR
      exact handleRescheduleSgiOnCore_preserves_contextMatchesCurrentOnCore st c st' hInv h hR
    · exact h

/-- The deferral keeps the core's match: a switch to the idle thread establishes
it, and the vacating fallback leaves the core no current thread. -/
theorem deferResidentElsewhere_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (deferResidentElsewhere st c) c := by
  unfold deferResidentElsewhere
  split
  · split
    · split
      · rename_i st' hS
        exact switchToThreadOnCore_establishes_contextMatchesCurrentOnCore st c _ st' hInv h hS
      · unfold contextMatchesCurrentOnCore
        simp
    · exact h
  · exact h

/-- **The settle keeps the executing core's bank its current thread's
context.** -/
theorem settleResidencyOnCore_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (settleResidencyOnCore st c) c := by
  have hY := deferResidentElsewhere_preserves_contextMatchesCurrentOnCore _ c
    (dispatchVacatedCore_preserves_objects_invExt c st hInv)
    (dispatchVacatedCore_preserves_contextMatchesCurrentOnCore st c hInv h)
  obtain ⟨hO, -, -, hCC, -, -⟩ := settleResidencyOnCore_frame st c
  refine (contextMatchesCurrentOnCore_frame ?_ ?_ hO).mpr hY
  · simp only [SchedulerState.currentOnCore, hCC]
  · simp only [settleResidencyOnCore, pokeReleasedResident_machine]; rfl

/-- A core with no current thread matches vacuously. -/
theorem contextMatchesCurrentOnCore_of_none {st : SystemState} {c : CoreId}
    (h : st.scheduler.currentOnCore c = none) : contextMatchesCurrentOnCore st c := by
  unfold contextMatchesCurrentOnCore; rw [h]; trivial

/-- The vacated save writes the store's table invariant through. -/
theorem saveVacatedFrameOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (rf saved : SeLe4n.RegisterFile) (hInv : st.objects.invExt) :
    (Architecture.saveVacatedFrameOnCore st c rf saved).objects.invExt := by
  unfold Architecture.saveVacatedFrameOnCore
  split
  · split
    · split
      · exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv
      · exact hInv
    · exact hInv
  · exact hInv

/-- The vacated save keeps the core's match: it writes a TCB only when the core
has no current thread. -/
theorem saveVacatedFrameOnCore_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (rf saved : SeLe4n.RegisterFile) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (Architecture.saveVacatedFrameOnCore st c rf saved) c := by
  cases hC : st.scheduler.currentOnCore c with
  | some tid => rw [Architecture.saveVacatedFrameOnCore_of_current st c rf saved tid hC]; exact h
  | none =>
    exact contextMatchesCurrentOnCore_of_none
      (by rw [Architecture.saveVacatedFrameOnCore_scheduler]; exact hC)

/-- The entry's save keeps the store's table invariant. -/
theorem saveCapturedTrapFrame_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    (Architecture.saveCapturedTrapFrame st c frame).objects.invExt := by
  cases frame with
  | none => exact hInv
  | some ic =>
    exact saveVacatedFrameOnCore_preserves_objects_invExt _ c _ _
      (Architecture.saveTrapFrameOnCore_preserves_objects_invExt st c _ hInv)

/-- **The entry's save establishes the executing core's match** (or keeps it,
when it saves nothing). -/
theorem saveCapturedTrapFrame_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt)
    (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (Architecture.saveCapturedTrapFrame st c frame) c := by
  cases frame with
  | none => exact h
  | some ic =>
    exact saveVacatedFrameOnCore_preserves_contextMatchesCurrentOnCore _ c _ _
      (Architecture.saveTrapFrameOnCore_contextMatchesCurrentOnCore st c _ hInv h)

/-- The settle then the activation keep the executing core's match, and the
entry's two ledger clears write neither the bank nor the store. -/
theorem settleThenActivateOnCore_preserves_contextMatchesCurrentOnCore (M : SystemState)
    (c : CoreId) (hInv : M.objects.invExt) (h : contextMatchesCurrentOnCore M c) :
    contextMatchesCurrentOnCore (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadOnCore (settleResidencyOnCore M c) c))) c := by
  have hA := activateThreadOnCore_preserves_contextMatchesCurrentOnCore _ c
    (settleResidencyOnCore_preserves_objects_invExt c M hInv)
    (settleResidencyOnCore_preserves_contextMatchesCurrentOnCore M c hInv h)
  obtain ⟨hO, -, hS, hM, -⟩ := Architecture.clearIcacheMaintenance_frame
    (Architecture.clearPhysicalWrites (activateThreadOnCore (settleResidencyOnCore M c) c))
  exact (contextMatchesCurrentOnCore_frame (by rw [hS]; rfl) (by rw [hM]; rfl)
    (by rw [hO]; rfl)).mpr hA

/-- **The reschedule entry keeps the executing core's bank its current thread's
context** (the secondary core's first entry is this one). -/
theorem perCoreRescheduleEntryState_preserves_contextMatchesCurrentOnCore (coreId : UInt64)
    (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv : st.objects.invExt) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) c := by
  obtain ⟨hlt, rfl⟩ := coreIdOfUInt64?_some hc
  simp only [activateThreadAt, PriorityInheritance.settleResidencyAt,
    Concurrency.saveCapturedTrapFrameAt, hc]
  have hSv := saveCapturedTrapFrame_preserves_objects_invExt st ⟨coreId.toNat, hlt⟩ frame hInv
  have hSc := saveCapturedTrapFrame_preserves_contextMatchesCurrentOnCore st ⟨coreId.toNat, hlt⟩
    frame hInv h
  refine settleThenActivateOnCore_preserves_contextMatchesCurrentOnCore _ _ ?_ ?_
  · show (perCoreRescheduleStep _ coreId).objects.invExt
    unfold perCoreRescheduleStep
    rw [dif_pos hlt]
    split
    · rename_i st' hR
      exact handleRescheduleSgiOnCore_preserves_objects_invExt _ _ st' hSv hR
    · exact hSv
  · show contextMatchesCurrentOnCore (perCoreRescheduleStep _ coreId) _
    unfold perCoreRescheduleStep
    rw [dif_pos hlt]
    split
    · rename_i st' hR
      exact handleRescheduleSgiOnCore_preserves_contextMatchesCurrentOnCore _ _ st' hSv hSc hR
    · exact hSc

/-- The per-core domain tick keeps the core's match: a domain switch's dispatch
establishes it, and the countdown writes neither the bank nor the store. -/
theorem scheduleDomainOnCoreState_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (scheduleDomainOnCoreState st c) c := by
  unfold scheduleDomainOnCoreState
  split
  · exact h
  · split
    · exact scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore _ c _
        (switchDomainOnCore_preserves_objects_invExt st c _ hInv (switchDomainOnCore_eq_state st c))
        (scheduleEffectiveOnCore_eq_state _ c)
    · exact (contextMatchesCurrentOnCore_frame rfl rfl rfl).mpr h

/-- The clock advance keeps every core's match: it writes only the timer. -/
theorem tickClockedState_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (tickClockedState st c) c := by
  unfold tickClockedState
  split
  · exact (contextMatchesCurrentOnCore_frame rfl rfl rfl).mpr h
  · exact h

/-- **The timer entry keeps the executing core's bank its current thread's
context.** -/
theorem perCoreTimerTickEntryState_preserves_contextMatchesCurrentOnCore (coreId : UInt64)
    (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv : st.objects.invExt) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) c := by
  obtain ⟨hlt, rfl⟩ := coreIdOfUInt64?_some hc
  simp only [activateThreadAt, PriorityInheritance.settleResidencyAt,
    Concurrency.saveCapturedTrapFrameAt, hc]
  have hSv := saveCapturedTrapFrame_preserves_objects_invExt st ⟨coreId.toNat, hlt⟩ frame hInv
  have hSc := saveCapturedTrapFrame_preserves_contextMatchesCurrentOnCore st ⟨coreId.toNat, hlt⟩
    frame hInv h
  generalize Architecture.saveCapturedTrapFrame st ⟨coreId.toNat, hlt⟩ frame = S at hSv hSc
  have hP : ((timerTickBracket coreId).run S).2 =
      perCoreTimerTickPost S ⟨coreId.toNat, hlt⟩ := by
    rw [timerTickBracket_run, perCoreTimerTickStepWithClockAdvance_state,
      perCoreTimerTickStep_valid_core S coreId hlt]
  rw [hP]
  have hK := tickClockedState_preserves_contextMatchesCurrentOnCore S ⟨coreId.toNat, hlt⟩ hSc
  have hKI : (tickClockedState S ⟨coreId.toNat, hlt⟩).objects.invExt := by
    rw [tickClockedState_objects]; exact hSv
  have hT := timerTickOnCore_preserves_contextMatchesCurrentOnCore _ _
    (timerTickOnCorePrepared_objects_invExt _ _ hKI)
    (timerTickOnCorePrepared_preserves_contextMatchesCurrentOnCore _ _ hKI hK)
  have hTI := timerTickOnCore_preserves_objects_invExt _ ⟨coreId.toNat, hlt⟩ hKI
  have hDI : (perCoreTimerTickPost S ⟨coreId.toNat, hlt⟩).objects.invExt :=
    scheduleDomainOnCore_preserves_objects_invExt _ ⟨coreId.toNat, hlt⟩ _ hTI
      (scheduleDomainOnCore_eq_state _ _)
  have hD : contextMatchesCurrentOnCore (perCoreTimerTickPost S ⟨coreId.toNat, hlt⟩)
      ⟨coreId.toNat, hlt⟩ :=
    scheduleDomainOnCoreState_preserves_contextMatchesCurrentOnCore _ ⟨coreId.toNat, hlt⟩ hTI hT
  generalize perCoreTimerTickPost S ⟨coreId.toNat, hlt⟩ = M at hDI hD
  exact settleThenActivateOnCore_preserves_contextMatchesCurrentOnCore M _ hDI hD

/-- A step that keeps the core's current slot and bank, and reads every thread
it holds back to one with the same saved registers, keeps the core's match. -/
theorem contextMatchesCurrentOnCore_of_regContext {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hRegs : st'.machine.regsOnCore c = st.machine.regsOnCore c)
    (hRC : ∀ tid tcb', st'.getTcb? tid = some tcb' →
      ∃ tcb, st.getTcb? tid = some tcb ∧ tcb'.registerContext = tcb.registerContext)
    (h : contextMatchesCurrentOnCore st c) : contextMatchesCurrentOnCore st' c := by
  unfold contextMatchesCurrentOnCore at h ⊢
  rw [hCur, hRegs]
  cases hC : st.scheduler.currentOnCore c with
  | none => trivial
  | some tid =>
    simp only [hC] at h
    dsimp only
    cases hT' : st'.getTcb? tid with
    | none => trivial
    | some tcb' =>
      obtain ⟨tcb, hT, hR⟩ := hRC tid tcb' hT'
      simp only [hT] at h
      dsimp only
      rw [hR]; exact h

/-- A TCB write that keeps the saved registers reads every thread back to one
with the same saved registers. -/
theorem updateTcb_registerContext_back (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).registerContext = x.registerContext)
    (tid : SeLe4n.ThreadId) (tcb' : TCB) (h : (st.updateTcb t f).getTcb? tid = some tcb') :
    ∃ tcb, st.getTcb? tid = some tcb ∧ tcb'.registerContext = tcb.registerContext := by
  by_cases hx : t.toObjId = tid.toObjId
  · obtain rfl := SeLe4n.ThreadId.toObjId_injective _ _ hx
    rw [SystemState.updateTcb_getTcb?_self st t f hInv] at h
    cases hT : st.getTcb? t with
    | none => rw [hT] at h; cases h
    | some x =>
      rw [hT] at h
      obtain rfl := Option.some.inj h
      exact ⟨x, rfl, hf x⟩
  · rw [SystemState.updateTcb_getTcb?_ne st t f hInv tid hx] at h
    exact ⟨tcb', h, rfl⟩

/-- Writing a thread's FP/SIMD context keeps every saved register. -/
theorem writeFpContextToTcb_registerContext_back (st : SystemState) (o : SeLe4n.ThreadId)
    (ctx : FpContext) (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId) (tcb' : TCB)
    (h : (Architecture.writeFpContextToTcb st o ctx).getTcb? tid = some tcb') :
    ∃ tcb, st.getTcb? tid = some tcb ∧ tcb'.registerContext = tcb.registerContext :=
  updateTcb_registerContext_back st o (fun t => { t with fpContext := ctx }) hInv (fun _ => rfl)
    tid tcb' h

/-- The FP/SIMD switch keeps the store's table invariant. -/
theorem fpAccessOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (live : Option FpContext) (hInv : st.objects.invExt) :
    (Architecture.fpAccessOnCore st c live).2.objects.invExt := by
  unfold Architecture.fpAccessOnCore
  repeat' split
  all_goals first
    | exact hInv
    | exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv

/-- **The FP/SIMD switch keeps the core's match**: it writes a thread's FP/SIMD
context and the core's FP owner, never a saved register or a bank. -/
theorem fpAccessOnCore_preserves_contextMatchesCurrentOnCore (st : SystemState) (c : CoreId)
    (live : Option FpContext) (hInv : st.objects.invExt) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (Architecture.fpAccessOnCore st c live).2 c := by
  unfold Architecture.fpAccessOnCore
  repeat' split
  all_goals first
    | exact h
    | exact contextMatchesCurrentOnCore_of_regContext (st := st) rfl rfl
        (fun _ _ ht => ⟨_, ht, rfl⟩) h
    | exact contextMatchesCurrentOnCore_of_regContext (st := st)
        (by simp [Architecture.writeFpContextToTcb, SystemState.updateTcb_scheduler])
        (by simp only [Architecture.setFpOwner, Architecture.writeFpContextToTcb_machine]; rfl)
        (fun tid tcb' ht => writeFpContextToTcb_registerContext_back st _ _ hInv tid tcb'
          (by simp only [Architecture.setFpOwner_getTcb?] at ht; exact ht)) h

/-- **The FP/SIMD entry keeps the executing core's bank its current thread's
context.** -/
theorem fpAccessEntryState_preserves_contextMatchesCurrentOnCore (coreId : UInt64)
    (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext) (st : SystemState)
    (hInv : st.objects.invExt) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (activateThreadAt (PriorityInheritance.settleResidencyAt
      (fpAccessEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2
        coreId) coreId) c := by
  simp only [activateThreadAt, PriorityInheritance.settleResidencyAt, fpAccessEntryStep,
    Concurrency.saveCapturedTrapFrameAt, hc]
  have hSv := saveCapturedTrapFrame_preserves_objects_invExt st c frame hInv
  have hSc := saveCapturedTrapFrame_preserves_contextMatchesCurrentOnCore st c frame hInv h
  generalize Architecture.saveCapturedTrapFrame st c frame = S at hSv hSc
  have hFI := fpAccessOnCore_preserves_objects_invExt S c live hSv
  have hF := fpAccessOnCore_preserves_contextMatchesCurrentOnCore S c live hSv hSc
  generalize (Architecture.fpAccessOnCore S c live).2 = F at hFI hF
  have hDI := dispatchVacatedCore_preserves_objects_invExt c F hFI
  have hD := dispatchVacatedCore_preserves_contextMatchesCurrentOnCore F c hFI hF
  generalize dispatchVacatedCore F c = M at hDI hD
  exact activateThreadOnCore_preserves_contextMatchesCurrentOnCore _ c
    (settleResidencyOnCore_preserves_objects_invExt c M hDI)
    (settleResidencyOnCore_preserves_contextMatchesCurrentOnCore M c hDI hD)

end SeLe4n.Kernel
