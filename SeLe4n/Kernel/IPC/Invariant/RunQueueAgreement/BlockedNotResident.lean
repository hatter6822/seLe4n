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
entry.  ZA6.19 carries it across the timer, fault, unknown-syscall and syscall
entries.
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

end BlockedNotResident

/-- The default state holds no resident. -/
theorem _root_.SeLe4n.Model.SystemState.default_blockedNotResident :
    (default : SystemState).blockedNotResident :=
  BlockedNotResident.of_defaultCodes rfl

/-- **A thread blocked in IPC is held by no core**: it is current nowhere
(`blockedCurrentNowhere`) and resident nowhere (`blockedNotResident`) — the
free-ness the census's writes to a blocked thread need (ZA6.15's cancellation
restore, ZA6.21's deliveries and reply). -/
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
