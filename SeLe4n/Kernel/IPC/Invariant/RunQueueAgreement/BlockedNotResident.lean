/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SavedRegisters

/-!
# A thread blocked in IPC is resident on no core

WS-ZA ZA6.16.  A core's resident thread (`MachineState.residentOnCore`) is one
whose live registers a remote deschedule left in that core's bank; the core's
next entry saves them over the thread's saved context.  The IPC writes that
name a blocked thread (a cancellation's restore, a delivery, a reply) are sound
only if that save cannot overwrite them, so a blocked thread must be resident on
no core.  A core records as resident only the thread it resumes at EL0, a ready
current thread, so `SystemState.blockedNotResident` holds whenever residency is
recorded; this file states it, proves it where no core holds a resident (boot,
the default state), carries it across a step that keeps the residency records
and the residents' IPC states, and gives the census's free-ness for a blocked
thread (`offCoreFree_of_blocked`).  ZA6.17 decomposes its preservation across
an entry (`BlockedNotResident.of_entry`).  ZA6.18 reads the other cores' half
off the entry's IPC-state frame (`readyKeptExcept`, which every run-queue
stage's `StateMono` gives), discharges both halves at the entry's tail
(`BlockedNotResident.of_tail`, the settle recording only the core's current
thread), and carries the invariant across the entries that block no thread: the
reschedule entry, the secondary core's first entry with it, and the FP/SIMD
entry.  ZA6.19 carries it across the timer entry, whose preemption windows keep
`StateMono`, and the fault and unknown-syscall entries, whose delivery blocks
only the executing core's current thread (`readyKeptStage`, the readiness frame
a blocking arm composes beside its block window).  ZA6.20 carries it across the
syscall entry.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-ZA ZA6.16: **every core's resident thread is ready in IPC**: a thread
blocked in IPC is resident on no core. -/
def _root_.SeLe4n.Model.SystemState.blockedNotResident (st : SystemState) : Prop :=
  ∀ (d : CoreId) (tid : SeLe4n.ThreadId) (t : TCB),
    st.machine.residentOnCore d = some tid → st.getTcb? tid = some t → t.ipcState = .ready

/-! ### The IPC-state frame an entry keeps -/

/-- WS-ZA ZA6.18: **a step that blocks no thread outside `S`**: a thread outside
`S` ready in IPC, or with no TCB, stays so.  Every run-queue stage is one for
every `S` (its `StateMono`); a block is one for a set holding the thread it
blocks. -/
def readyKeptExcept (S : SeLe4n.ThreadId → Prop) (st st' : SystemState) : Prop :=
  ∀ t, ¬ S t → st.readyOrAbsent t → st'.readyOrAbsent t

theorem readyKeptExcept.trans {S : SeLe4n.ThreadId → Prop} {a b c : SystemState}
    (h1 : readyKeptExcept S a b) (h2 : readyKeptExcept S b c) : readyKeptExcept S a c :=
  fun t hS h => h2 t hS (h1 t hS h)

theorem readyKeptExcept.of_stateMono {S : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    (h : SystemState.StateMono st st') : readyKeptExcept S st st' :=
  fun _ _ hr => h.readyOrAbsent hr

namespace BlockedNotResident

/-- A state no core holds a resident in satisfies it. -/
theorem of_noResidents {st : SystemState} (h : ∀ d, st.machine.residentOnCore d = none) :
    st.blockedNotResident :=
  fun d _ _ hR _ => absurd (hR.symm.trans (h d)) (by simp)

/-- A machine whose residency codes are the default's holds no resident. -/
theorem of_defaultCodes {st : SystemState}
    (h : st.machine.residentCode = (default : SystemState).machine.residentCode) :
    st.blockedNotResident :=
  of_noResidents fun d => by
    simp [MachineState.residentOnCore, h, CurrentNotResidentElsewhere.default_residentCode,
      SeLe4n.PerCoreVector.get_eq_getElem]

/-- **It carries across a step that records no new resident and keeps each
resident's IPC state.** -/
theorem of_frame {X Y : SystemState} (h : X.blockedNotResident)
    (hR : ∀ d tid, Y.machine.residentOnCore d = some tid → X.machine.residentOnCore d = some tid)
    (hT : ∀ tid t', Y.getTcb? tid = some t' → ∃ t, X.getTcb? tid = some t ∧ t.ipcState = t'.ipcState) :
    Y.blockedNotResident := fun d tid t' hY hT' => by
  obtain ⟨t, hX, hS⟩ := hT tid t' hT'
  rw [← hS]; exact h d tid t (hR d tid hY) hX

/-- WS-ZA ZA6.17: **the entry's decomposition.**  After a step on core `e`, the
residents are of two kinds.  A resident of another core was resident there
before (`residentKeptOffCore`, the coverage relation's `residentKept`), so it was
ready if it had a TCB; it stays ready, or without a TCB, if the step left such a
thread on another core so (`hKeep`, the frame that the step blocks no thread
another core holds).  The resident of `e` is the one `e`'s own settle recorded,
its current thread resumed at EL0, which is ready (`hOwn`).  ZA6.18 reads both
halves in `readyOrAbsent`, so a TCB a step creates (a retype's, ready) needs no
TCB before it. -/
theorem of_entry {e : CoreId} {pre post : SystemState} (h : pre.blockedNotResident)
    (hRK : residentKeptOffCore e pre post)
    (hKeep : ∀ d, d ≠ e → ∀ tid, post.machine.residentOnCore d = some tid →
      pre.readyOrAbsent tid → post.readyOrAbsent tid)
    (hOwn : ∀ tid, post.machine.residentOnCore e = some tid → post.readyOrAbsent tid) :
    post.blockedNotResident := fun d tid t' hR hT' => by
  by_cases hd : d = e
  · subst hd; exact hOwn tid hR t' hT'
  · exact hKeep d hd tid hR (fun t hT => h d tid t (hRK d hd tid hR) hT) t' hT'

/-- WS-ZA ZA6.18: **the two halves at an entry's tail.**  `hKeep`: the entry
blocked no thread but the one current on `e` before it, and that thread is
resident on no other core (`currentNotResidentElsewhere`).  `hOwn`: `e`'s
resident is its current thread, which is runnable between scheduling points
(`currentDequeuedUnique`), so ready. -/
theorem of_tail {e : CoreId} {pre post : SystemState} (h : pre.blockedNotResident)
    (hC : pre.currentNotResidentElsewhere) (hRK : residentKeptOffCore e pre post)
    (hKeep : readyKeptExcept (fun t => pre.scheduler.currentOnCore e = some t) pre post)
    (hOwn : ∀ tid, post.machine.residentOnCore e = some tid →
      post.scheduler.currentOnCore e = some tid)
    (hD : post.currentDequeuedUnique) : post.blockedNotResident :=
  of_entry h hRK
    (fun d hd tid hR => hKeep tid fun hCur =>
      hC.elsewhere e d tid (Ne.symm hd) hCur (hC.residentNotIdle d tid (hRK d hd tid hR))
        (hRK d hd tid hR))
    (fun tid hR x hx => by
      obtain ⟨y, hy, hr⟩ := hD.runnable (hOwn tid hR)
      rw [hx] at hy; cases hy; exact hr.1)

/-- A step that keeps every residency record and blocks no thread keeps it. -/
theorem of_kept {X Y : SystemState} (h : X.blockedNotResident)
    (hR : Y.machine.residentCode = X.machine.residentCode)
    (hK : readyKeptExcept (fun _ => False) X Y) : Y.blockedNotResident :=
  fun d tid t' hY hT' => by
    have hX : X.machine.residentOnCore d = some tid := by
      simp only [MachineState.residentOnCore, hR] at hY ⊢; exact hY
    exact hK tid id (fun t hT => h d tid t hX hT) t' hT'

theorem _root_.SeLe4n.Kernel.currentDequeuedUnique_of_clearLedgers {X : SystemState}
    (h : (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites X)).currentDequeuedUnique) :
    X.currentDequeuedUnique :=
  SystemState.currentDequeuedUniqueExcept_of_eq
    (st := Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites X)) rfl
    (fun _ _ => rfl) (SystemState.StateMono.of_objects rfl) h

theorem clearLedgers {X : SystemState} (h : X.blockedNotResident) :
    (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites X)).blockedNotResident :=
  h

/-- ...and in the syscall step's order. -/
theorem clearLedgers' {X : SystemState} (h : X.blockedNotResident) :
    (Architecture.clearPhysicalWrites
      (Architecture.clearIcacheMaintenance X)).blockedNotResident :=
  h

end BlockedNotResident

/-- The default state holds no resident. -/
theorem _root_.SeLe4n.Model.SystemState.default_blockedNotResident :
    (default : SystemState).blockedNotResident :=
  BlockedNotResident.of_defaultCodes rfl

/-- **A thread blocked in IPC is held by no core**: it is current nowhere
(`blockedCurrentNowhere`) and resident nowhere (`blockedNotResident`) — the
free-ness the census's writes to a blocked thread need (ZA6.15's cancellation
restore, ZA6.22's deliveries and reply). -/
theorem offCoreFree_of_blocked {e : CoreId} {st : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hB : blockedCurrentNowhere st) (hN : st.blockedNotResident)
    (hT : st.getTcb? tid = some t) (hS : t.ipcState ≠ .ready) : offCoreFree e st tid :=
  fun d _ => ⟨hB tid t hT hS d, fun h => hS (hN d tid t h hT)⟩

/-! ### The scheduler's steps block no thread

Each is a switch or a stage, so its `StateMono` keeps every thread's IPC state
ready; the entry stages that package them keep only the placement half. -/

/-- The reschedule handler: a switch, a drop or nothing, then the flag clear. -/
theorem handleRescheduleSgiOnCore_stateMono {st st' : SystemState} {c : CoreId}
    (h : handleRescheduleSgiOnCore st c = .ok st') (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) : SystemState.StateMono st st' := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · cases h
  · split at h
    · rw [Except.ok.injEq] at h; subst h
      exact ((dropCurrentOnCore_runQueueSwitchStage st c).trans_stage
        (SystemState.RunQueueStage.clearReschedulePendingOnCore _ _)).2.2 hInv hR
    · rw [Except.ok.injEq] at h; subst h
      exact (SystemState.RunQueueStage.clearReschedulePendingOnCore _ _).2.2 hInv hR
  · rename_i tid hChoose
    split at h
    · split at h
      · rename_i hSw
        rw [Except.ok.injEq] at h; subst h
        exact ((switchToThreadOnCore_runQueueSwitchStage hSw (fun hRf => .inl
          (SystemState.queuedOn_of_mem_runQueueOnCore hRf
            ((RunQueue.mem_toList_iff_mem _ _).mp
              (chooseThreadEffectiveOnCore_some_mem_runQueueOnCore st c tid (hRf c)
                hChoose))))).trans_stage
          (SystemState.RunQueueStage.clearReschedulePendingOnCore _ _)).2.2 hInv hR
      · split at h
        · rw [Except.ok.injEq] at h; subst h
          exact ((dropCurrentOnCore_runQueueSwitchStage st c).trans_stage
            (SystemState.RunQueueStage.clearReschedulePendingOnCore _ _)).2.2 hInv hR
        · rw [Except.ok.injEq] at h; subst h
          exact (SystemState.RunQueueStage.clearReschedulePendingOnCore _ _).2.2 hInv hR
    · rw [Except.ok.injEq] at h; subst h
      exact (SystemState.RunQueueStage.clearReschedulePendingOnCore _ _).2.2 hInv hR

theorem dispatchVacatedCore_stateMono (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) :
    SystemState.StateMono st (PriorityInheritance.dispatchVacatedCore st c) := by
  unfold PriorityInheritance.dispatchVacatedCore
  split
  · exact .refl _
  · split
    · rename_i hRs; exact handleRescheduleSgiOnCore_stateMono hRs hInv hR
    · exact .refl _

theorem deferResidentElsewhere_stateMono (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) :
    SystemState.StateMono st (PriorityInheritance.deferResidentElsewhere st c) := by
  unfold PriorityInheritance.deferResidentElsewhere
  split
  · split
    · split
      · rename_i hS
        exact (switchToThreadOnCore_runQueueSwitchStage hS fun _ => .inr (.inr rfl)).2.2 hInv hR
      · exact (dropCurrentOnCore_runQueueSwitchStage st c).2.2 hInv hR
    · exact .refl _
  · exact .refl _

/-- **The settle and the activation block no thread.** -/
theorem settleThenActivateOnCore_stateMono (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) :
    SystemState.StateMono st
      (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore st c) c) := by
  have D := dispatchVacatedCore_runQueueEntryStage st c
  obtain ⟨hInvD, hRD⟩ := D.1.links hInv hR
  obtain ⟨hInvY, hRY⟩ := (deferResidentElsewhere_runQueueEntryStage _ c).1.links hInvD hRD
  obtain ⟨hO, hQ, hE, -, -, -⟩ := PriorityInheritance.settleResidencyOnCore_frame st c
  have hRS := SystemState.runQueueRefined_of_frame
    (fun c t => SystemState.runLinkOn_of_objects hO c t) hQ hE hRY
  exact ((dispatchVacatedCore_stateMono st c hInv hR).trans
    ((deferResidentElsewhere_stateMono _ c hInvD hRD).trans
      (SystemState.StateMono.of_objects hO))).trans
    ((activateThreadOnCore_runQueueStage _ c).2.2 (hO ▸ hInvY) hRS)

/-- The settle records as `c`'s resident only its current thread. -/
theorem settleThenActivateOnCore_residentCurrent (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId)
    (h : (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore st c) c
      ).machine.residentOnCore c = some tid) :
    (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore st c) c
      ).scheduler.currentOnCore c = some tid := by
  rw [activateThreadOnCore_residentOnCore, PriorityInheritance.settleResidencyOnCore_resident] at h
  rw [activateThreadOnCore_scheduler, PriorityInheritance.settleResidencyOnCore_currentOnCore]
  split at h
  · exact h
  · cases h

/-- WS-ZA ZA6.18: **the settle and the activation on core `e` keep a thread
blocked in IPC resident on no core**, after a step on `e` that recorded no new
resident off `e` and blocked no thread but `e`'s current one, into a state
between scheduling points. -/
theorem settleThenActivateOnCore_blockedNotResident {e : CoreId} {pre M : SystemState}
    (h : pre.blockedNotResident) (hC : pre.currentNotResidentElsewhere)
    (hInvM : M.objects.invExt) (hRM : M.runQueueRefined) (hRK : residentKeptOffCore e pre M)
    (hKeep : readyKeptExcept (fun t => pre.scheduler.currentOnCore e = some t) pre M)
    (hD : (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e
      ).currentDequeuedUnique) :
    (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore M e) e).blockedNotResident :=
  BlockedNotResident.of_tail h hC
    (residentKeptOffCore_trans hRK fun d hd tid hR =>
      (settleResidencyOnCore_stepCovers e M hInvM).residentKept d hd tid
        (by rw [activateThreadOnCore_residentOnCore] at hR; exact hR))
    (hKeep.trans (.of_stateMono (settleThenActivateOnCore_stateMono M e hInvM hRM)))
    (settleThenActivateOnCore_residentCurrent M e) hD

/-- ...for a per-core entry's raw core id: on an id naming no core the entry
recorded no resident and blocked no thread. -/
theorem settleThenActivateAt_blockedNotResident {pre M : SystemState} {coreId : UInt64}
    (h : pre.blockedNotResident) (hC : pre.currentNotResidentElsewhere)
    (hInvM : M.objects.invExt) (hRM : M.runQueueRefined)
    (hK : ∀ c, Concurrency.coreIdOfUInt64? coreId = some c → residentKeptOffCore c pre M ∧
      readyKeptExcept (fun t => pre.scheduler.currentOnCore c = some t) pre M)
    (hN : Concurrency.coreIdOfUInt64? coreId = none →
      M.machine.residentCode = pre.machine.residentCode ∧ readyKeptExcept (fun _ => False) pre M)
    (hD : (activateThreadAt (PriorityInheritance.settleResidencyAt M coreId) coreId
      ).currentDequeuedUnique) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt M coreId) coreId).blockedNotResident := by
  unfold activateThreadAt PriorityInheritance.settleResidencyAt at hD ⊢
  cases hc : Concurrency.coreIdOfUInt64? coreId with
  | none => exact BlockedNotResident.of_kept h (hN hc).1 (hN hc).2
  | some c =>
    rw [hc] at hD
    exact settleThenActivateOnCore_blockedNotResident h hC hInvM hRM (hK c hc).1 (hK c hc).2 hD

/-! ### The entries that block no thread -/

theorem perCoreRescheduleStep_stateMono (st : SystemState) (coreId : UInt64)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) :
    SystemState.StateMono st (perCoreRescheduleStep st coreId) := by
  unfold perCoreRescheduleStep
  split
  · split
    · rename_i hRs; exact handleRescheduleSgiOnCore_stateMono hRs hInv hR
    · exact .refl _
  · exact .refl _

/-- WS-ZA ZA6.18: **the reschedule entry keeps a thread blocked in IPC resident
on no core** (the secondary core's first entry is this one): it blocks no
thread. -/
theorem perCoreRescheduleEntryState_preserves_blockedNotResident (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hC : st.currentNotResidentElsewhere) (hB : st.blockedNotResident) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))
      ).blockedNotResident := by
  have S := perCoreRescheduleEntryState_runQueueEntryStage coreId frame st
  have hD := S.2 hInv0 hR0 (S.1.links hInv0 hR0).2 hD0
  have hSv := saveCapturedTrapFrameAt_runQueueStage st coreId frame
  obtain ⟨hInvS, hRS⟩ := hSv.1.links hInv0 hR0
  have hM : SystemState.StateMono st (perCoreRescheduleStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId) :=
    (hSv.2.2 hInv0 hR0).trans (perCoreRescheduleStep_stateMono _ coreId hInvS hRS)
  obtain ⟨hInvM, hRM⟩ := (perCoreRescheduleStep_runQueueEntryStage _ coreId).1.links hInvS hRS
  refine BlockedNotResident.clearLedgers
    (settleThenActivateAt_blockedNotResident hB hC hInvM hRM ?_ ?_
      (currentDequeuedUnique_of_clearLedgers hD))
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine ⟨(keptOffCore_of_save_stepCovers (saveCapturedTrapFrameAt_scheduler st coreId frame)
      (saveCapturedTrapFrameAt_residentCode st coreId frame) ?_).2, .of_stateMono hM⟩
    show stepCovers _ _ (perCoreRescheduleStep _ coreId)
    unfold perCoreRescheduleStep
    rw [dif_pos h]
    split
    · rename_i st' h'
      exact handleRescheduleSgiOnCore_stepCovers _ _ st' hInvS h'
    · exact stepCovers_refl _ _
  · intro hc
    refine ⟨?_, .of_stateMono hM⟩
    show (perCoreRescheduleStep _ coreId).machine.residentCode = _
    rw [perCoreRescheduleStep_invalid_core _ coreId (not_lt_of_coreIdOfUInt64?_none hc)]
    exact saveCapturedTrapFrameAt_residentCode st coreId frame

/-- WS-ZA ZA6.18: **the FP/SIMD entry keeps a thread blocked in IPC resident on
no core**: it switches FP/SIMD state and dispatches a vacated core, and blocks
no thread. -/
theorem fpAccessEntryState_preserves_blockedNotResident (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hC : st.currentNotResidentElsewhere) (hB : st.blockedNotResident) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId)
        coreId).blockedNotResident := by
  have St := fpAccessEntryState_runQueueEntryStage coreId frame live st
  have hD := St.2 hInv0 hR0 (St.1.links hInv0 hR0).2 hD0
  have hSv := saveCapturedTrapFrameAt_runQueueStage st coreId frame
  obtain ⟨hInvS, hRS⟩ := hSv.1.links hInv0 hR0
  have hM : (fpAccessEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId
        live).2.objects.invExt ∧
      (fpAccessEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId
        live).2.runQueueRefined ∧
      SystemState.StateMono st (fpAccessEntryStep
        (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 := by
    unfold fpAccessEntryStep
    cases Concurrency.coreIdOfUInt64? coreId with
    | none => exact ⟨hInvS, hRS, hSv.2.2 hInv0 hR0⟩
    | some c =>
      have F := fpAccessOnCore_runQueueStage (Concurrency.saveCapturedTrapFrameAt st coreId frame)
        c live
      obtain ⟨hI, hR⟩ := F.1.links hInvS hRS
      obtain ⟨hI', hR'⟩ := (dispatchVacatedCore_runQueueEntryStage _ c).1.links hI hR
      exact ⟨hI', hR', (hSv.2.2 hInv0 hR0).trans ((F.2.2 hInvS hRS).trans
        (dispatchVacatedCore_stateMono _ c hI hR))⟩
  refine settleThenActivateAt_blockedNotResident hB hC hM.1 hM.2.1 ?_ ?_ hD
  · intro c hc
    refine ⟨?_, .of_stateMono hM.2.2⟩
    have hFp : (Architecture.fpAccessOnCore
        (Concurrency.saveCapturedTrapFrameAt st coreId frame) c live).2.objects.invExt :=
      ((fpAccessOnCore_runQueueStage _ c live).1.links hInvS hRS).1
    unfold fpAccessEntryStep
    rw [hc]
    exact (keptOffCore_of_save_stepCovers
      (by rw [Architecture.fpAccessOnCore_scheduler, saveCapturedTrapFrameAt_scheduler])
      (by rw [fpAccessOnCore_residentCode, saveCapturedTrapFrameAt_residentCode])
      (dispatchVacatedCore_stepCovers c _ hFp)).2
  · intro hc
    refine ⟨?_, .of_stateMono hM.2.2⟩
    unfold fpAccessEntryStep
    rw [hc]
    exact saveCapturedTrapFrameAt_residentCode st coreId frame

/-! ### The timer entry

A preemption blocks no thread: a preemption window keeps `StateMono`
(`RunQueueWindowStage`'s third clause), and so does the dispatch that closes it. -/

/-- **A preemption point opened and closed blocks no thread.** -/
theorem windowDispatch_stateMono {c : CoreId} {st st' st'' : SystemState}
    (h1 : SystemState.RunQueueWindowStage (.preempt c) st st')
    (h2 : SystemState.RunQueueDispatchStage c st' st'') (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) : SystemState.StateMono st st'' :=
  let ⟨h', r'⟩ := h1.1 hInv hR
  (h1.2.2 c rfl hInv hR).trans (h2.2.2 h' r')

/-- The domain switch: the outgoing thread's requeue, then the vacated slot. -/
theorem switchDomainOnCore_stateMono {st st' : SystemState} {c : CoreId}
    (h : switchDomainOnCore st c = .ok st') (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) : SystemState.StateMono st st' := by
  unfold switchDomainOnCore at h
  split at h
  · cases h; exact .refl _
  · dsimp only at h
    split at h
    · cases h
    · cases h
      refine windowDispatch_stateMono (requeueOutgoingOnCore_runQueueWindowStage st c)
        (vacateCurrent_runQueueDispatchStage rfl rfl rfl fun c' => ?_) hInv hR
      show _ = if c' = c then _ else _
      by_cases hc : c' = c
      · subst hc; simp
      · rw [if_neg hc]
        simp only [SchedulerState.setDomainScheduleIndexOnCore_currentOnCore,
          SchedulerState.setDomainTimeRemainingOnCore_currentOnCore,
          SchedulerState.setActiveDomainOnCore_currentOnCore]
        exact SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc)

theorem scheduleDomainOnCore_stateMono {st st' : SystemState} {c : CoreId}
    (h : scheduleDomainOnCore st c = .ok st') (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) : SystemState.StateMono st st' := by
  unfold scheduleDomainOnCore at h
  split at h
  · cases h; exact .refl _
  · split at h
    · split at h
      · cases h
      · rename_i stD hD
        obtain ⟨hI, hR'⟩ := (switchDomainOnCore_runQueueEntryStage hD).1 hInv hR
        exact (switchDomainOnCore_stateMono hD hInv hR).trans
          ((scheduleEffectiveOnCore_runQueueDispatchStage h).2.2 hI hR')
    · cases h
      exact (SystemState.RunQueueStage.of_frame rfl rfl rfl).2.2 hInv hR

/-- **The per-core tick blocks no thread**: the drain, the charge (whose budget
exhaustion times out IPC waiters, which makes them ready) and the reschedule. -/
theorem timerTickOnCore_stateMono (st : SystemState) (c : CoreId)
    (hH : (timerTickOnCorePrepared st c).currentContextPlaceableOnCore c)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) :
    SystemState.StateMono st (timerTickOnCore st c) := by
  have hP : SystemState.RunQueueStage st (timerTickOnCorePrepared st c) :=
    (SystemState.RunQueueStage.of_frame (st := st)
      (st' := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] })
      rfl rfl rfl).trans
      (processReplenishmentsDueOnCore_runQueueStage
      { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } c st.machine.timer)
  have hRr : ∀ s, SystemState.RunQueueStage st s →
      SystemState.StateMono st (rescheduleIfPendingOnCore s c) := fun s hs => by
    unfold rescheduleIfPendingOnCore
    split
    · obtain ⟨hI, hR'⟩ := hs.1 hInv hR
      exact (hs.2.2 hInv hR).trans
        (handleRescheduleSgiOnCore_stateMono (handleRescheduleSgiOnCore_eq_state s c) hI hR')
    · exact hs.2.2 hInv hR
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hB, h⟩ <;> rw [h]
  · exact hRr _ hP
  · exact hRr _ hP
  · obtain ⟨hI, hR'⟩ := hP.1 hInv hR
    exact (hP.2.2 hInv hR).trans (windowDispatch_stateMono
      (timerTickBudgetOnCore_runQueueWindowStage hB hCur hH)
      (scheduleEffectiveOnCore_runQueueDispatchStage (scheduleEffectiveOnCore_eq_state st3 c)) hI hR')
  · exact hRr _ (hP.trans (timerTickBudgetOnCore_runQueueStage_of_not_preempted hB))

/-- The per-core timer step: the boot core's clock, the tick, the domain
accounting. -/
theorem perCoreTimerTickStep_stateMono (st : SystemState) (coreId : UInt64)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hRef : st.releaseQueueRefined)
    (hD : st.currentDequeuedUnique) (hBi : schedContextBindingBidirectional st)
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore st d) :
    SystemState.StateMono st (perCoreTimerTickStep st coreId).1 := by
  by_cases hc : coreId.toNat < Concurrency.numCores
  · rw [perCoreTimerTickStep_valid_core st coreId hc]
    have hClk : SystemState.RunQueueStage st (tickClockedState st ⟨coreId.toNat, hc⟩) := by
      unfold tickClockedState; split
      · exact SystemState.RunQueueStage.of_frame rfl rfl rfl
      · exact SystemState.RunQueueStage.refl _
    have hCInv : (tickClockedState st ⟨coreId.toNat, hc⟩).objects.invExt := by
      rw [tickClockedState_objects]; exact hInv
    have hCRef : (tickClockedState st ⟨coreId.toNat, hc⟩).releaseQueueRefined := by
      unfold tickClockedState; split <;> exact hRef
    have hCBi : schedContextBindingBidirectional (tickClockedState st ⟨coreId.toNat, hc⟩) := by
      unfold tickClockedState; split <;> exact hBi
    have hCAff : ∀ d, replenishQueueAffinityConsistentOnCore
        (tickClockedState st ⟨coreId.toNat, hc⟩) d := by
      unfold tickClockedState; split <;> exact hAff
    have hCD : (tickClockedState st ⟨coreId.toNat, hc⟩).currentDequeuedUnique :=
      SystemState.currentDequeuedUniqueExcept_of_eq (st := st)
        (by rw [tickClockedState_scheduler])
        (fun c t => by unfold SystemState.runLinkOn SystemState.getTcb?; rw [tickClockedState_objects])
        (SystemState.StateMono.of_objects (tickClockedState_objects _ _)) hD
    have hPl := timerTickOnCorePrepared_currentContextPlaceableOnCore _ ⟨coreId.toNat, hc⟩
      hCInv hCRef hCD hCBi hCAff
    obtain ⟨-, hR1⟩ := hClk.1 hInv hR
    obtain ⟨hI2, hR2⟩ := (timerTickOnCore_runQueueEntryStage _ _ hPl).1 hCInv hR1
    exact ((hClk.2.2 hInv hR).trans (timerTickOnCore_stateMono _ _ hPl hCInv hR1)).trans
      (scheduleDomainOnCore_stateMono (scheduleDomainOnCore_eq_state _ _) hI2 hR2)
  · rw [perCoreTimerTickStep_invalid_core st coreId hc]
    exact .refl _

/-- WS-ZA ZA6.19: **the timer entry keeps a thread blocked in IPC resident on
no core**: it blocks no thread.  The tick reads its placement premises at the
saved state, as its stage does
(`perCoreTimerTickEntryState_runQueueEntryStage`). -/
theorem perCoreTimerTickEntryState_preserves_blockedNotResident (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hInv : (Concurrency.saveCapturedTrapFrameAt st coreId frame).objects.invExt)
    (hRef : (Concurrency.saveCapturedTrapFrameAt st coreId frame).releaseQueueRefined)
    (hD : (Concurrency.saveCapturedTrapFrameAt st coreId frame).currentDequeuedUnique)
    (hBi : schedContextBindingBidirectional (Concurrency.saveCapturedTrapFrameAt st coreId frame))
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) d)
    (hC : st.currentNotResidentElsewhere) (hB : st.blockedNotResident) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))
      ).blockedNotResident := by
  have S := perCoreTimerTickEntryState_runQueueEntryStage coreId frame st hInv hRef hD hBi hAff
  have hDf := S.2 hInv0 hR0 (S.1.links hInv0 hR0).2 hD0
  have hSv := saveCapturedTrapFrameAt_runQueueStage st coreId frame
  obtain ⟨hInvS, hRS⟩ := hSv.1.links hInv0 hR0
  have hM : SystemState.StateMono st (perCoreTimerTickStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId).1 :=
    (hSv.2.2 hInv0 hR0).trans
      (perCoreTimerTickStep_stateMono _ coreId hInvS hRS hRef hD hBi hAff)
  obtain ⟨hInvM, hRM⟩ :=
    (perCoreTimerTickStep_runQueueEntryStage _ coreId hInv hRef hD hBi hAff).1.links hInvS hRS
  refine BlockedNotResident.clearLedgers
    (settleThenActivateAt_blockedNotResident hB hC hInvM hRM ?_ ?_
      (currentDequeuedUnique_of_clearLedgers hDf))
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    exact ⟨(keptOffCore_of_save_stepCovers (saveCapturedTrapFrameAt_scheduler st coreId frame)
      (saveCapturedTrapFrameAt_residentCode st coreId frame)
      (perCoreTimerTickStep_stepCovers _ coreId h hInv hBi hD)).2, .of_stateMono hM⟩
  · intro hc
    refine ⟨?_, .of_stateMono hM⟩
    show (perCoreTimerTickStep _ coreId).1.machine.residentCode = _
    rw [perCoreTimerTickStep_invalid_core _ coreId (not_lt_of_coreIdOfUInt64?_none hc)]
    exact saveCapturedTrapFrameAt_residentCode st coreId frame

/-! ### The fault and unknown-syscall entries

A fault delivery blocks the faulting thread and no other: the handler call
blocks its caller (the blocking arm's IPC-state store, `readyKeptStage` off the
caller), and every other step of the delivery is a run-queue stage or a
dispatch, which keeps `StateMono`. -/

/-- **A step that keeps readiness off the threads `S`**, given the link
invariants at its start: the readiness frame a blocking arm composes. -/
def readyKeptStage (S : SeLe4n.ThreadId → Prop) (st st' : SystemState) : Prop :=
  st.objects.invExt → st.runQueueRefined → readyKeptExcept S st st'

namespace readyKeptStage

variable {S : SeLe4n.ThreadId → Prop}

theorem refl (st : SystemState) : readyKeptStage S st st := fun _ _ _ _ h => h

theorem of_stage {st st' : SystemState} (h : SystemState.RunQueueStage st st') :
    readyKeptStage S st st' := fun hI hR => .of_stateMono (h.2.2 hI hR)

theorem of_dispatch {c : CoreId} {st st' : SystemState}
    (h : SystemState.RunQueueDispatchStage c st st') : readyKeptStage S st st' :=
  fun hI hR => .of_stateMono (h.2.2 hI hR)

/-- Two readiness frames compose over the link invariants the first step keeps. -/
theorem trans {a b c : SystemState} (L : SystemState.RunQueueLinkStage a b)
    (h1 : readyKeptStage S a b) (h2 : readyKeptStage S b c) : readyKeptStage S a c :=
  fun hI hR => let ⟨hI', hR'⟩ := L.links hI hR; (h1 hI hR).trans (h2 hI' hR')

theorem mono {S' : SeLe4n.ThreadId → Prop} {st st' : SystemState} (hS : ∀ t, S t → S' t)
    (h : readyKeptStage S st st') : readyKeptStage S' st st' :=
  fun hI hR t hn => h hI hR t fun hs => hn (hS t hs)

end readyKeptStage

/-- **A TCB update that keeps a ready thread ready keeps every thread's
readiness.** -/
theorem readyKeptExcept_updateTcb {S : SeLe4n.ThreadId → Prop} (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : TCB → TCB) (hInv : st.objects.invExt)
    (hf : ∀ x, x.ipcState = .ready → (f x).ipcState = .ready) :
    readyKeptExcept S st (st.updateTcb tid f) := fun t _ h x hx => by
  by_cases e : t = tid
  · subst e
    rw [SystemState.updateTcb_getTcb?_self st t f hInv] at hx
    cases hT : st.getTcb? t with
    | none => rw [hT] at hx; cases hx
    | some y =>
      rw [hT] at hx; cases hx
      exact hf y (h y hT)
  · rw [SystemState.updateTcb_getTcb?_ne st tid f hInv t
      (fun h' => e (ThreadId.toObjId_injective _ _ h').symm)] at hx
    exact h x hx

/-- **The blocking arm's IPC-state store keeps every other thread's readiness**:
it writes the one TCB. -/
theorem storeTcbIpcStateAndMessage_readyKeptStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {s : ThreadIpcState} {m : Option IpcMessage}
    (h : storeTcbIpcStateAndMessage st tid s m = .ok st') :
    readyKeptStage (· = tid) st st' := fun hI _ t hn hr x hx => by
  obtain ⟨_, _, hS⟩ := modifyTcb_ok_decompose h
  rw [storeObject_getTcb?_ne st st' _ _ t
    (fun h' => hn (ThreadId.toObjId_injective _ _ h')) hI hS] at hx
  exact hr x hx

/-- **The cross-core call blocks only its caller**: the receiver's hand-over
and wake are run-queue stages, the caller's block is its IPC-state store, and
the deschedule closing the window is a dispatch. -/
theorem endpointCallOnCore_readyKeptStage (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload) (c : CoreId)
    (st : SystemState) (hHeads : endpointHeadsWakeable st)
    (hCur : st.scheduler.currentOnCore c = some caller) (hNI : isIdleThreadId caller = false) :
    readyKeptStage (· = caller) st (endpointCallOnCore endpointId caller payload c st).1 := by
  unfold endpointCallOnCore
  split
  · rename_i ep hEp
    split
    · rename_i r hHead
      split
      · exact .refl _
      · rename_i receiver tcb st1 hPop
        split
        · exact .refl _
        · rename_i st2 hS2
          have hN : st2.currentNowhere receiver := (hHeads.popped hPop).of_scheduler_eq
            (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS2)
          have hC2 : st2.scheduler.currentOnCore c = some caller :=
            currentOnCore_of_scheduler_eq (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS2)
              (currentOnCore_of_scheduler_eq (endpointQueuePopHead_scheduler_eq _ _ _ _ _ hPop) hCur)
          have hC3 : (wakeThread st2 receiver c).1.scheduler.currentOnCore c = some caller := by
            show (enqueueRunnableOnCore st2 _ receiver).scheduler.currentOnCore c = _
            rw [enqueueRunnableOnCore_currentOnCore]; exact hC2
          split
          · exact .refl _
          · rename_i st4 hS4
            split
            · exact .refl _
            · rename_i st5 hS5
              have hC5 : st5.scheduler.currentOnCore c = some caller :=
                currentOnCore_of_scheduler_eq (linkServerStashedReply_scheduler_eq _ _ _ _ hS5)
                  (currentOnCore_of_scheduler_eq
                    (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS4) hC3)
              have P := ((endpointQueuePopHead_runQueueStage hPop).trans
                (storeTcbIpcStateAndMessage_runQueueStage hS2 rfl)).then_wake c hN
                (hHeads.popped_blocked hPop)
              have W := storeTcbIpcStateAndMessage_runQueueBlockStage hS4 hC3 hNI
              have L5 := linkServerStashedReply_runQueueStage hS5
              have D := SystemState.RunQueueDispatchStage.descheduleCurrent st5 c caller hC5
              exact (readyKeptStage.of_stage P).trans P.1
                ((storeTcbIpcStateAndMessage_readyKeptStage hS4).trans W.1
                ((readyKeptStage.of_stage L5).trans L5.1
                ((readyKeptStage.of_dispatch D).trans D.1
                (readyKeptStage.of_stage (SystemState.linkReplyWaiter_runQueueStage _ caller
                  receiver)))))
    · split
      · exact .refl _
      · rename_i st1 hE
        split
        · exact .refl _
        · rename_i st2 hS2
          have hC1 : st1.scheduler.currentOnCore c = some caller :=
            currentOnCore_of_scheduler_eq (endpointQueueEnqueue_scheduler_eq _ _ _ _ _ hE) hCur
          have E1 := endpointQueueEnqueue_runQueueStage hE
          have W := storeTcbIpcStateAndMessage_runQueueBlockStage hS2 hC1 hNI
          have D := SystemState.RunQueueDispatchStage.descheduleCurrent st2 c caller
            (currentOnCore_of_scheduler_eq
              (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS2) hC1)
          exact (readyKeptStage.of_stage E1).trans E1.1
            ((storeTcbIpcStateAndMessage_readyKeptStage hS2).trans W.1
            ((readyKeptStage.of_dispatch D).trans D.1
            (readyKeptStage.of_stage (recordSendCap_runQueueStage _ caller _ _))))
  · split <;> exact .refl _

theorem endpointCallWithCapsOnCore_readyKeptStage (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (base : SeLe4n.Slot) (c : CoreId) (st : SystemState)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some caller)
    (hNI : isIdleThreadId caller = false) :
    readyKeptStage (· = caller) st
      (endpointCallWithCapsOnCore endpointId caller payload base c st).1 := by
  have s0 := (endpointCallOnCore_runQueueEntryStage endpointId caller payload c st hHeads hCur hNI).1
  have r0 := endpointCallOnCore_readyKeptStage endpointId caller payload c st hHeads hCur hNI
  unfold endpointCallWithCapsOnCore
  generalize endpointCallOnCore endpointId caller payload c st = r at s0 r0 ⊢
  obtain ⟨st1, r⟩ := r
  cases r with
  | error e => exact r0
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact r0
      | (rename_i hU; exact r0.trans s0 (.of_stage (receiveTransferCaps_runQueueStage hU)))

theorem endpointCallCrossCoreDispatch_readyKeptStage (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (base : SeLe4n.Slot) (c : CoreId) (st : SystemState)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some caller)
    (hNI : isIdleThreadId caller = false) :
    readyKeptStage (· = caller) st
      (endpointCallCrossCoreDispatch endpointId caller payload base c st).1 := by
  have s0 := (endpointCallWithCapsOnCore_runQueueEntryStage endpointId caller payload base c st
    hHeads hCur hNI).1
  have r0 := endpointCallWithCapsOnCore_readyKeptStage endpointId caller payload base c st
    hHeads hCur hNI
  unfold endpointCallCrossCoreDispatch
  generalize endpointCallWithCapsOnCore endpointId caller payload base c st = r at s0 r0 ⊢
  obtain ⟨st1, r⟩ := r
  cases r with
  | error e => exact r0
  | ok res =>
    dsimp only
    repeat' split
    all_goals first
      | exact r0
      | (rename_i hD; exact r0.trans s0 (.of_stage ((applyCallDonationOnCore_runQueueStage hD).trans
          (PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _))))

/-- **The fault suspend keeps every thread's readiness**: the deschedule is a
stage, and the off-queue write sets the thread state, not the IPC state. -/
theorem faultSuspendOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop} (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) : readyKeptStage S st (faultSuspendOnCore st tid c) :=
  have hS := SystemState.RunQueueStage.runDescheduleOnCore st c tid
  (readyKeptStage.of_stage hS).trans hS.1
    fun hI _ => readyKeptExcept_updateTcb _ tid _ hI fun _ h => h

/-- **The fault delivery blocks only the faulting thread**: the handler call, or
the fail-closed suspend; then the woken handler's frame and the fault record. -/
theorem faultDeliverOnCore_readyKeptStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (f : Fault) (fctx : FaultContext) (c : CoreId)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some tid)
    (hNI : isIdleThreadId tid = false) :
    readyKeptStage (· = tid) st (faultDeliverOnCore st tid f fctx c).1 := by
  have sus := (faultSuspendOnCore_readyKeptStage (S := (· = tid)) st tid c).trans
    (faultSuspendOnCore_runQueueEntryStage st tid c hCur hNI).1
    (.of_stage (recordPendingFault_runQueueStage _ tid { fault := f, context := fctx }))
  unfold faultDeliverOnCore
  split
  · exact sus
  · rename_i tgt _
    have s0 := (endpointCallCrossCoreDispatch_runQueueEntryStage tgt.endpoint tid
      (SendPayload.fault f fctx tgt.cap.badge) (SeLe4n.Slot.ofNat 0) c st hHeads hCur hNI).1
    have r0 := endpointCallCrossCoreDispatch_readyKeptStage tgt.endpoint tid
      (SendPayload.fault f fctx tgt.cap.badge) (SeLe4n.Slot.ofNat 0) c st hHeads hCur hNI
    generalize endpointCallCrossCoreDispatch tgt.endpoint tid
      (SendPayload.fault f fctx tgt.cap.badge) (SeLe4n.Slot.ofNat 0) c st = r at s0 r0 ⊢
    obtain ⟨st1, r⟩ := r
    cases r with
    | error e => exact sus
    | ok res =>
      exact r0.trans s0 (.of_stage ((stageWokenDelivery_runQueueStage _ _ _).trans
        (recordPendingFault_runQueueStage _ _ _)))

theorem faultDeliverOnCoreChecked_readyKeptStage (ctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext) (c : CoreId)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some tid)
    (hNI : isIdleThreadId tid = false) :
    readyKeptStage (· = tid) st (faultDeliverOnCoreChecked ctx st tid f fctx c).1 := by
  have sus := (faultSuspendOnCore_readyKeptStage (S := (· = tid)) st tid c).trans
    (faultSuspendOnCore_runQueueEntryStage st tid c hCur hNI).1
    (.of_stage (recordPendingFault_runQueueStage _ tid { fault := f, context := fctx }))
  unfold faultDeliverOnCoreChecked
  split
  · exact sus
  · split
    · exact faultDeliverOnCore_readyKeptStage st tid f fctx c hHeads hCur hNI
    · exact sus

/-- **The executing core's successor blocks no thread**: the reschedule, or
nothing. -/
theorem scheduleLocalSuccessorFrom_stateMono (caller? : Option SeLe4n.ThreadId)
    (post : SystemState) (c : CoreId) (hInv : post.objects.invExt) (hR : post.runQueueRefined) :
    SystemState.StateMono post (PriorityInheritance.scheduleLocalSuccessorFrom caller? post c) := by
  unfold PriorityInheritance.scheduleLocalSuccessorFrom
  split
  · split
    · rename_i h; exact handleRescheduleSgiOnCore_stateMono h hInv hR
    · exact .refl _
  · exact .refl _

/-- **The delivery both fault entries share blocks only the executing core's
current thread**: a vacated core's dispatch blocks none, and the delivery
blocks the faulting thread, which is that core's current thread. -/
theorem faultEntryDeliver_readyKeptStage (lctx : LabelingContext) (st : SystemState)
    (f : Fault) (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (hHeads : endpointHeadsWakeable st) :
    readyKeptStage (fun t => st.scheduler.currentOnCore c = some t) st
      (faultEntryDeliver lctx st f ectx w c).2 := by
  unfold faultEntryDeliver
  split
  · exact fun hI hR => .of_stateMono (dispatchVacatedCore_stateMono st c hI hR)
  · rename_i tid hCur
    dsimp only
    split
    · exact .refl _
    · rename_i hIdle
      intro hI hR
      have hNI : isIdleThreadId tid = false := by simpa using hIdle
      have D := faultDeliveredState_runQueueEntryStage lctx st f ectx w c _ hI hHeads hCur hNI
      have hW := writeFaultRegistersToTcb_runQueueStage st tid w
      have r1 : readyKeptStage (· = tid) st (faultDeliveredState lctx st f ectx w c tid) :=
        (readyKeptStage.of_stage hW).trans hW.1
          (faultDeliverOnCoreChecked_readyKeptStage lctx _ tid f _ c
            (hHeads.updateTcb hI fun _ => rfl)
            (by rw [writeFaultRegistersToTcb_scheduler]; exact hCur) hNI)
      exact (readyKeptStage.mono (fun t (h : t = tid) => by subst h; exact hCur)
        (r1.trans D.1 fun hI' hR' =>
          .of_stateMono (scheduleLocalSuccessorFrom_stateMono _ _ c hI' hR'))) hI hR

/-- WS-ZA ZA6.19: **the fault entry keeps a thread blocked in IPC resident on
no core**: it blocks only the faulting thread, the executing core's current
thread (`faultEntryDeliver_readyKeptStage`). -/
theorem faultEntryState_preserves_blockedNotResident (lctx : LabelingContext)
    (coreId : UInt64) (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hC : st.currentNotResidentElsewhere) (hB : st.blockedNotResident) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx
        (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).blockedNotResident := by
  have St := faultEntryState_runQueueEntryStage lctx coreId frame ectx w st E
  have hDf := St.2 hInv0 hR0 (St.1.links hInv0 hR0).2 hD0
  have hS := saveCapturedTrapFrameAt_runQueueStage st coreId (some frame)
  obtain ⟨hInvS, hRS⟩ := hS.1.links hInv0 hR0
  have ES := E.of_ipcFrame hS (saveCapturedTrapFrameAt_ipcFrame st coreId _)
  obtain ⟨hInvM, hRM⟩ :=
    (faultEntryStep_runQueueEntryStage lctx _ ectx w coreId ES).1.links hInvS hRS
  have hSM := hS.2.2 hInv0 hR0
  refine BlockedNotResident.clearLedgers
    (settleThenActivateAt_blockedNotResident hB hC hInvM hRM ?_ ?_
      (currentDequeuedUnique_of_clearLedgers hDf))
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine ⟨(keptOffCore_of_save_stepCovers
      (saveCapturedTrapFrameAt_scheduler st coreId (some frame))
      (saveCapturedTrapFrameAt_residentCode st coreId (some frame)) ?_).2,
      (readyKeptExcept.of_stateMono hSM).trans ((?_ : readyKeptStage _ _ _) hInvS hRS)⟩
    · unfold faultEntryStep
      rw [dif_pos h]
      split
      · split
        · exact stepCovers_refl _ _
        · exact faultEntryDeliver_stepCovers lctx _ _ ectx w _ hInvS
      · exact stepCovers_refl _ _
    · unfold faultEntryStep
      rw [dif_pos h]
      split
      · split
        · exact .refl _
        · exact (faultEntryDeliver_readyKeptStage lctx _ _ ectx w _ ES.endpointHeads).mono
            fun t ht => by rwa [saveCapturedTrapFrameAt_scheduler] at ht
      · exact .refl _
  · intro hc
    unfold faultEntryStep
    rw [dif_neg (not_lt_of_coreIdOfUInt64?_none hc)]
    exact ⟨saveCapturedTrapFrameAt_residentCode st coreId (some frame), .of_stateMono hSM⟩

/-- WS-ZA ZA6.19: **the unknown-syscall entry keeps a thread blocked in IPC
resident on no core**: its delivery is the fault entry's. -/
theorem unknownSyscallEntryState_preserves_blockedNotResident (lctx : LabelingContext)
    (coreId : UInt64) (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hC : st.currentNotResidentElsewhere) (hB : st.blockedNotResident) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).blockedNotResident := by
  have St := unknownSyscallEntryState_runQueueEntryStage lctx coreId frame ectx w st E
  have hDf := St.2 hInv0 hR0 (St.1.links hInv0 hR0).2 hD0
  have hS := saveCapturedSyscallFrameAt_runQueueStage st coreId (some frame)
  have hF : IpcFrame st (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) := by
    unfold Concurrency.saveCapturedSyscallFrameAt
    split
    · exact saveCapturedSyscallFrame_ipcFrame st _ _
    · exact IpcFrame.refl _
  obtain ⟨hInvS, hRS⟩ := hS.1.links hInv0 hR0
  have ES := E.of_ipcFrame hS hF
  obtain ⟨hInvM, hRM⟩ :=
    (unknownSyscallEntryStep_runQueueEntryStage lctx _ ectx w coreId ES).1.links hInvS hRS
  have hSM := hS.2.2 hInv0 hR0
  refine BlockedNotResident.clearLedgers
    (settleThenActivateAt_blockedNotResident hB hC hInvM hRM ?_ ?_
      (currentDequeuedUnique_of_clearLedgers hDf))
  · intro c hc
    obtain ⟨h, rfl⟩ := coreIdOfUInt64?_some hc
    refine ⟨(keptOffCore_of_save_stepCovers
      (saveCapturedSyscallFrameAt_scheduler st coreId (some frame))
      (saveCapturedSyscallFrameAt_residentCode st coreId (some frame)) ?_).2,
      (readyKeptExcept.of_stateMono hSM).trans ((?_ : readyKeptStage _ _ _) hInvS hRS)⟩
    · unfold unknownSyscallEntryStep
      rw [dif_pos h]
      split
      · exact faultEntryDeliver_stepCovers lctx _ _ ectx w _ hInvS
      · exact stepCovers_refl _ _
    · unfold unknownSyscallEntryStep
      rw [dif_pos h]
      split
      · exact (faultEntryDeliver_readyKeptStage lctx _ _ ectx w _ ES.endpointHeads).mono
          fun t ht => by rwa [saveCapturedSyscallFrameAt_scheduler] at ht
      · exact .refl _
  · intro hc
    unfold unknownSyscallEntryStep
    rw [dif_neg (not_lt_of_coreIdOfUInt64?_none hc)]
    exact ⟨saveCapturedSyscallFrameAt_residentCode st coreId (some frame), .of_stateMono hSM⟩

end SeLe4n.Kernel

namespace SeLe4n.Platform.Boot
open SeLe4n.Model
open SeLe4n.Kernel

/-- WS-ZA ZA6.16: **the state the started boot installs holds no blocked
resident** — it holds no resident at all
(`bootFromPlatformCheckedWithIdleThreadsFor_ok_residentCode`). -/
theorem bootFromPlatformCheckedStartedFor_blockedNotResident
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ist.state.blockedNotResident := by
  obtain ⟨base, started, hBase, hStart, rfl⟩ := bootFromPlatformCheckedStartedFor_ok cores config ist h
  refine BlockedNotResident.of_defaultCodes ?_
  rw [linkBootCapabilities_machine, startInitialThreads_machine _ _ _ hStart]
  exact bootFromPlatformCheckedWithIdleThreadsFor_ok_residentCode cores config base hBase

end SeLe4n.Platform.Boot
