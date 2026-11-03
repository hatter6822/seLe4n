/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SavedRegistersDispatch
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.EntryContextMatches

/-!
# Every other core's bank still matches its current thread after an entry

WS-ZA ZA6.28.  A core `d`'s bank match (`contextMatchesCurrentOnCore st d`)
reads three things: `d`'s current slot, `d`'s bank and the saved registers of
`d`'s current thread.  An entry on another core `e` keeps all three for `d`:

* it makes no thread current on `d` (`stepCovers.currentKept`);
* it writes no bank but `e`'s (`stepCovers.banksKept`, WS-ZA ZA6.13);
* it writes the saved registers of no thread current on another core
  (`currentSavedRegsKeptOffCore`, the current-thread half of the
  saved-register census `savedRegsKeptOffCore`, WS-ZA ZA6.14 to ZA6.26).

`contextMatchesCurrentOnCore_offCore` composes the three.  A core the entry
vacates has no current thread, so its match holds vacuously; the thread it
still runs at EL0 is its resident, whose frame the core's next entry saves
(`Architecture.saveVacatedFrameOnCore`), and the remote stall waits on that
save before the initiator resumes anything (WS-ZA ZA6.11).

The composition is closed at the syscall entry
(`syscallDispatchEntryState_preserves_contextMatchesCurrentOffCore`), the
reschedule entry, the FP/SIMD entry, the fault entry and the unknown-syscall
entry; the timer entry's is in `TimerContextMatches`, and the executing core's
match through the syscall seam in `ExecutingContextMatches`.

**The deferral writes no saved register.**  The residency settle's deferral
(`PriorityInheritance.deferResidentElsewhere`) preempts a thread another core
still holds as resident, and the preemption saves the executing core's bank
into the thread's saved context.  The deferral now reloads that context into
the bank first, so on both of its branches (the switch to the idle thread and
the fallback when the switch fails) the save writes back what the context
already holds (`deferResidentElsewhere_savedRegs`), and the whole settle
writes no saved register (`settleResidencyOnCore_savedRegs`).
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)
open SeLe4n.Kernel.PriorityInheritance

/-! ## The current-thread half of the census -/

/-- **The step writes the saved registers of no thread current on a core other
than `e`**: every such thread after the step has the saved registers it had
before.  The half of `savedRegsKeptOffCore` a bank match reads. -/
def currentSavedRegsKeptOffCore (e : CoreId) (pre post : SystemState) : Prop :=
  ∀ d, d ≠ e → ∀ t, post.scheduler.currentOnCore d = some t → post.savedRegs t = pre.savedRegs t

theorem currentSavedRegsKeptOffCore_refl (e : CoreId) (st : SystemState) :
    currentSavedRegsKeptOffCore e st st :=
  fun _ _ _ _ => rfl

/-- The half composes through the second step's frame of the current slots. -/
theorem currentSavedRegsKeptOffCore_trans {e : CoreId} {a b c : SystemState}
    (h₁ : currentSavedRegsKeptOffCore e a b) (h₂ : currentSavedRegsKeptOffCore e b c)
    (hK : currentKeptOffCore e b c) : currentSavedRegsKeptOffCore e a c :=
  fun d hd t ht => (h₂ d hd t ht).trans (h₁ d hd t (hK d hd t ht))

/-- The census gives its current-thread half. -/
theorem currentSavedRegsKeptOffCore_of_savedRegsKeptOffCore {e : CoreId} {pre post : SystemState}
    (h : savedRegsKeptOffCore e pre post) : currentSavedRegsKeptOffCore e pre post :=
  fun d hd t ht => h d hd t (.inl ht)

/-- A step that writes no saved register. -/
theorem currentSavedRegsKeptOffCore_of_eq {e : CoreId} {pre post : SystemState}
    (h : ∀ t, post.savedRegs t = pre.savedRegs t) : currentSavedRegsKeptOffCore e pre post :=
  fun _ _ t _ => h t

/-- **A step that writes only threads current on no other core after it.** -/
theorem currentSavedRegsKeptOffCore_of_kept {e : CoreId} {pre post : SystemState}
    {W : SeLe4n.ThreadId → Prop} (h : savedRegsKeptExcept W pre post)
    (hW : ∀ t, W t → ∀ d, d ≠ e → post.scheduler.currentOnCore d ≠ some t) :
    currentSavedRegsKeptOffCore e pre post :=
  fun d hd t ht => h t fun hw => hW t hw d hd ht

/-- **A step that writes only the executing core's current thread**, on a
state where no thread is current on two cores and the step moves no current
slot off the executing core. -/
theorem currentSavedRegsKeptOffCore_of_current {e : CoreId} {pre post : SystemState}
    (h : savedRegsKeptExcept (fun t => pre.scheduler.currentOnCore e = some t) pre post)
    (hU : currentsUnique pre) (hK : currentKeptOffCore e pre post) :
    currentSavedRegsKeptOffCore e pre post :=
  currentSavedRegsKeptOffCore_of_kept h fun _ ht d hd hd' => hd (hU e d _ ht (hK d hd _ hd'))

/-- **Every other core's bank match is kept** by a step that makes no thread
current on another core, writes no other core's bank, and writes the saved
registers of no thread current on another core. -/
theorem contextMatchesCurrentOnCore_offCore {e : CoreId} {pre post : SystemState}
    (hK : currentKeptOffCore e pre post) (hB : banksKeptOffCore e pre post)
    (hS : currentSavedRegsKeptOffCore e pre post) (d : CoreId) (hd : d ≠ e)
    (h : contextMatchesCurrentOnCore pre d) : contextMatchesCurrentOnCore post d := by
  unfold contextMatchesCurrentOnCore at h ⊢
  cases hC : post.scheduler.currentOnCore d with
  | none => trivial
  | some t =>
    dsimp only
    have hPre := hK d hd t hC
    have hR := hS d hd t hC
    rw [hPre] at h
    simp only at h
    unfold SystemState.savedRegs at hR
    cases hT : post.getTcb? t with
    | none => trivial
    | some tcb' =>
      rw [hT] at hR
      cases hT0 : pre.getTcb? t with
      | none => rw [hT0] at hR; cases hR
      | some tcb =>
        rw [hT0] at hR h
        simp only [Option.map_some, Option.some.injEq] at hR
        dsimp only
        rw [hB d hd, hR]; exact h

/-! ## The settle and the activation -/

/-- **A preemption on a matching core writes no saved register**: the bank it
saves into the outgoing thread is the thread's saved context already. -/
theorem preemptCurrentOnCore_savedRegs_of_match (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hM : contextMatchesCurrentOnCore st c) (t : SeLe4n.ThreadId) :
    (preemptCurrentOnCore st c incoming).savedRegs t = st.savedRegs t := by
  by_cases hC : st.scheduler.currentOnCore c = some t
  · cases hT : st.getTcb? t with
    | none =>
      by_cases hI : (t == incoming) = true
      · have hId : preemptCurrentOnCore st c incoming = st := by
          unfold preemptCurrentOnCore; rw [hC]; simp only [hI, if_true]
        rw [hId]
      · rw [preemptCurrentOnCore_noop_of_prev_no_tcb st c incoming t hC hI hT]
    | some tcb =>
      obtain ⟨tcb', hT', hR⟩ := preemptCurrentOnCore_getTcb?_regContext st c incoming t tcb hInv hT
      have hBank : st.machine.regsOnCore c = tcb.registerContext := by
        unfold contextMatchesCurrentOnCore at hM
        rw [hC] at hM; simp only [hT] at hM
        exact (SeLe4n.RegisterFile.beq_iff_eq' _ _).mp hM
      unfold SystemState.savedRegs
      rw [hT', hT]
      simp only [Option.map_some, Option.some.injEq]
      rcases hR with hR | ⟨-, hR⟩
      · exact hR
      · exact hR.trans hBank
  · exact preemptCurrentOnCore_savedRegsKeptExcept st c incoming hInv t hC

/-- The reload makes the executing core's bank its current thread's saved
context, so the core matches. -/
theorem restoreIncomingContextOnCore_current_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (hC : st.scheduler.currentOnCore c = some tid) :
    contextMatchesCurrentOnCore (restoreIncomingContextOnCore st c tid) c := by
  unfold contextMatchesCurrentOnCore
  rw [restoreIncomingContextOnCore_scheduler, hC]
  dsimp only
  rw [restoreIncomingContextOnCore_getTcb?]
  cases hT : st.getTcb? tid with
  | none => trivial
  | some tcb =>
    dsimp only
    rw [restoreIncomingContextOnCore_regsOnCore_self st c tid tcb hT]
    exact SeLe4n.RegisterFile.beq_self _

/-- WS-ZA ZA6.28: **the deferral writes no saved register.**  It reloads the
deferred thread's saved context into the bank, so the preemption on either
branch, the switch to the idle thread or the fallback that vacates the core,
saves back what the context already holds. -/
theorem deferResidentElsewhere_savedRegs (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    (deferResidentElsewhere st c).savedRegs t = st.savedRegs t := by
  unfold deferResidentElsewhere
  split
  · rename_i tid hC
    split
    · dsimp only
      have hI : (restoreIncomingContextOnCore st c tid).objects.invExt := by
        rw [restoreIncomingContextOnCore_objects]; exact hInv
      have hM := restoreIncomingContextOnCore_current_contextMatchesCurrentOnCore st c tid hC
      have hR : (restoreIncomingContextOnCore st c tid).savedRegs t = st.savedRegs t :=
        savedRegsKeptExcept.of_objects_eq (W := fun _ => False)
          (restoreIncomingContextOnCore_objects st c tid) t id
      have hP := preemptCurrentOnCore_savedRegs_of_match _ c (idleThreadId c) hI hM t
      split
      · rename_i st' hS
        have hO := switchToThreadOnCore_ok_objects _ st' c _ hS
        rw [← hR, ← hP]
        exact ((savedRegsKeptExcept.of_runLinks (W := fun _ => False)
          (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ c _)).trans
          (savedRegsKeptExcept.of_objects_eq hO)) t id
      · rw [← hR, ← hP]
        exact savedRegsKeptExcept.of_objects_eq (W := fun _ => False)
          (dropCurrentOnCore_objects _ c) t id
    · rfl
  · rfl

/-- **The vacated core's dispatch writes no saved register**: it runs only on a
core with no current thread, whose scheduling point saves nobody. -/
theorem dispatchVacatedCore_savedRegs (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    (dispatchVacatedCore st c).savedRegs t = st.savedRegs t := by
  unfold dispatchVacatedCore
  split
  · rfl
  · rename_i hC
    split
    · rename_i st' hR
      rw [handleRescheduleSgiOnCore_eq_state] at hR
      cases hR
      exact handleRescheduleOnCoreState_savedRegsKeptExcept st c hInv t (by rw [hC]; simp)
    · rfl

/-- WS-ZA ZA6.28: **the residency settle writes no saved register**: the
vacated core's dispatch saves nobody, the deferral saves back what each context
holds, and the record and the poke write no object. -/
theorem settleResidencyOnCore_savedRegs (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    (settleResidencyOnCore st c).savedRegs t = st.savedRegs t := by
  have hO : (settleResidencyOnCore st c).objects =
      (deferResidentElsewhere (dispatchVacatedCore st c) c).objects := by
    simp only [settleResidencyOnCore, pokeReleasedResident_objects]
  rw [show (settleResidencyOnCore st c).savedRegs t =
      (deferResidentElsewhere (dispatchVacatedCore st c) c).savedRegs t from
    savedRegsKeptExcept.of_objects_eq (W := fun _ => False) hO t id,
    deferResidentElsewhere_savedRegs _ c (dispatchVacatedCore_preserves_objects_invExt c st hInv) t,
    dispatchVacatedCore_savedRegs st c hInv t]

/-- `setConsumed` writes the saved registers of the thread it names alone. -/
theorem setConsumed_savedRegsKeptExcept (st : SystemState) (s : SeLe4n.SchedContextId)
    (y : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    savedRegsKeptExcept (· = y) st (setConsumed st s y) := by
  unfold setConsumed
  split
  · exact (savedRegsKeptExcept.updateSchedContext st s _ hInv).trans
      (.updateTcb_written _ y _ (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv)
        rfl)
  · exact .refl _

/-- The yield completion writes the saved registers of its yielder alone. -/
theorem completeYieldTo_savedRegsKeptExcept (st : SystemState) (y : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : savedRegsKeptExcept (· = y) st (completeYieldTo st y) := by
  unfold completeYieldTo
  split
  · split
    · exact .refl _
    · exact (setConsumed_savedRegsKeptExcept st _ y hInv).trans
        (cancelYieldTo_savedRegsKeptExcept _ y
          (SystemState.setConsumed_preserves_objects_invExt _ _ _ hInv))
  · exact .refl _

/-- **The activation writes the saved registers of the core's current thread
alone.** -/
theorem activateThreadOnCore_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st
      (activateThreadOnCore st c) := by
  rcases activateThreadOnCore_objects st c with h | ⟨tid, hC, h⟩
  · exact .of_objects_eq h
  · exact (completeYieldTo_savedRegsKeptExcept st tid hInv).mono
      (fun t ht => by rw [hC, ht]) |>.trans (.of_objects_eq (pre := completeYieldTo st tid) h)

/-! ## The entry's save -/

/-- The trap-frame save writes the saved registers of the core's current thread
alone. -/
theorem saveTrapFrameOnCore_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) (hInv : st.objects.invExt) :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st
      (Architecture.saveTrapFrameOnCore st c rf) := by
  rcases Architecture.saveTrapFrameOnCore_frame st c rf with h | ⟨tid, _, _, hCur, _, h⟩
  · rw [h]; exact .refl _
  · intro t ht
    rw [h]
    exact savedRegs_updateTcb_ne hInv (fun hE => ht (hE ▸ hCur))

/-- The vacated save writes the saved registers of the vacated core's resident
alone. -/
theorem saveVacatedFrameOnCore_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (rf saved : SeLe4n.RegisterFile) (hInv : st.objects.invExt) :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = none ∧
      st.machine.residentOnCore c = some t) st
      (Architecture.saveVacatedFrameOnCore st c rf saved) := by
  intro t ht
  unfold Architecture.saveVacatedFrameOnCore
  split
  · split
    · rename_i tid hC hR
      split
      · exact savedRegs_updateTcb_ne hInv (fun hE => ht ⟨hC, hE ▸ hR⟩)
      · rfl
    · rfl
  · rfl

/-- The vacated save writes no machine state. -/
theorem saveVacatedFrameOnCore_machine (st : SystemState) (c : CoreId)
    (rf saved : SeLe4n.RegisterFile) :
    (Architecture.saveVacatedFrameOnCore st c rf saved).machine = st.machine := by
  unfold Architecture.saveVacatedFrameOnCore
  split
  · split
    · split
      · exact SystemState.updateTcb_machine _ _ _
      · rfl
    · rfl
  · rfl

/-- **The entry's save keeps every other core's bank match**: it writes the
executing core's bank, the saved registers of the executing core's current
thread, which no other core runs (`currentsUnique`), and on a vacated core
those of its resident, which no core runs as a current thread
(`currentNotResidentElsewhere`). -/
theorem saveTrapThenVacated_contextMatchesCurrentOnCore_offCore (st : SystemState)
    (c : CoreId) (rf saved : SeLe4n.RegisterFile) (hInv : st.objects.invExt)
    (hU : currentsUnique st) (hN : st.currentNotResidentElsewhere) (d : CoreId) (hd : d ≠ c)
    (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore
      (Architecture.saveVacatedFrameOnCore (Architecture.saveTrapFrameOnCore st c rf) c rf saved)
      d := by
  have hS1 := Architecture.saveTrapFrameOnCore_scheduler st c rf
  have hInv1 := Architecture.saveTrapFrameOnCore_preserves_objects_invExt st c rf hInv
  have hSc : (Architecture.saveVacatedFrameOnCore (Architecture.saveTrapFrameOnCore st c rf) c rf
      saved).scheduler = st.scheduler := by
    rw [Architecture.saveVacatedFrameOnCore_scheduler, hS1]
  have hFr := Architecture.saveTrapFrameOnCore_frame st c rf
  have hRes1 : (Architecture.saveTrapFrameOnCore st c rf).machine.residentOnCore c =
      st.machine.residentOnCore c := by
    rcases hFr with h | ⟨_, _, _, _, _, h⟩
    · rw [h]
    · rw [h]; rfl
  refine contextMatchesCurrentOnCore_offCore (e := c)
    (currentKeptOffCore_of_eq fun _ _ => by rw [hSc]) ?_ ?_ d hd h
  · intro d' hd'
    rw [saveVacatedFrameOnCore_machine]
    rcases hFr with h | ⟨_, _, _, _, _, h⟩
    · rw [h]
    · rw [h]; exact MachineState.regsOnCore_setRegsOnCore_ne st.machine c d' rf (Ne.symm hd')
  · refine currentSavedRegsKeptOffCore_of_kept (W := fun t =>
      st.scheduler.currentOnCore c = some t ∨
        (st.scheduler.currentOnCore c = none ∧ st.machine.residentOnCore c = some t))
      (((saveTrapFrameOnCore_savedRegsKeptExcept st c rf hInv).mono fun _ h => .inl h).trans
        ((saveVacatedFrameOnCore_savedRegsKeptExcept _ c rf saved hInv1).mono
          fun _ h => .inr (by rw [hS1, hRes1] at h; exact h))) ?_
    intro t hW d' hd' hC'
    rw [hSc] at hC'
    rcases hW with hW | ⟨-, hR⟩
    · exact hd' (hU c d' t hW hC')
    · cases hI : isIdleThreadId t
      · exact hN.elsewhere d' c t hd' hC' hI hR
      · exact absurd (hN.residentNotIdle c t hR) (by rw [hI]; decide)

/-- Syncing the entry's IPC-buffer words keeps every core's bank match: it
writes the entry's words alone. -/
theorem syncUserWords_contextMatchesCurrentOnCore (st : SystemState) (bytes : ByteArray)
    (n : Nat) (d : CoreId) (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore (Architecture.IpcBufferRead.syncUserWords st bytes n) d := by
  obtain ⟨b, k, hE⟩ := Architecture.IpcBufferRead.syncUserWords_eq_words st bytes n
  rw [hE]; exact h

/-! ## The syscall seam and the syscall entry -/

/-- The other entries' ledger clears keep every core's bank match. -/
theorem contextMatchesCurrentOnCore_clearLedgers {X : SystemState} {d : CoreId}
    (h : contextMatchesCurrentOnCore X d) :
    contextMatchesCurrentOnCore
      (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites X)) d :=
  h

/-- The syscall step's ledger clears keep every core's bank match. -/
theorem contextMatchesCurrentOnCore_clearLedgers' {X : SystemState} {d : CoreId}
    (h : contextMatchesCurrentOnCore X d) :
    contextMatchesCurrentOnCore
      (Architecture.clearPhysicalWrites (Architecture.clearIcacheMaintenance X)) d :=
  h

/-- WS-ZA ZA6.28: **the syscall commit tail writes the saved registers of no
thread current on another core**: the caller's return staging writes the caller,
which no other core held at the entry's start (`base`); the local scheduling
point and the activation each write the executing core's current thread, current
nowhere else; and the residency settle writes no saved register
(`settleResidencyOnCore_savedRegs`). -/
theorem syscallCommitTail_currentSavedRegsKeptOffCore {e : CoreId} {base post : SystemState}
    (caller? : Option SeLe4n.ThreadId) (o : Architecture.SyscallOutcome)
    (hInv : post.objects.invExt) (hRef : post.runQueueRefined)
    (hDU : post.currentDequeuedUnique)
    (hFree : ∀ tid, caller? = some tid → offCoreFree e base tid)
    (hK : currentKeptOffCore e base post) (hR : residentKeptOffCore e base post) :
    currentSavedRegsKeptOffCore e post (activateThreadOnCore (settleResidencyOnCore
      (PriorityInheritance.scheduleLocalSuccessorFrom caller?
        (Architecture.stageCallerReturnFor caller? post e o) e) e) e) := by
  obtain ⟨hStage, hStageInv⟩ := stageCallerReturnFor_stepCovers e caller? post o hInv
  have hSucc := scheduleLocalSuccessorFrom_stepCovers e caller? _ hStageInv
  have hSuccInv := scheduleLocalSuccessorFrom_preserves_objects_invExt e caller? _ hStageInv
  have hSettle := settleResidencyOnCore_stepCovers e _ hSuccInv
  have hSettleInv := settleResidencyOnCore_preserves_objects_invExt e _ hSuccInv
  have hAct := activateThreadOnCore_stepCovers e _ hSettleInv
  have uniq : ∀ {X : SystemState}, SystemState.RunQueueEntryStage post X → currentsUnique X :=
    fun St => currentsUnique_of_dequeuedUnique (St.2 hInv hRef (St.1.links hInv hRef).2 hDU)
  have B := (stageCallerReturnFor_runQueueStage caller? post e o).entry
  have Full := (B.trans (scheduleLocalSuccessorFrom_runQueueEntryStage caller? _ e)).trans
    (settleThenActivateOnCore_runQueueEntryStage _ e)
  have c2 : currentSavedRegsKeptOffCore e post
      (Architecture.stageCallerReturnFor caller? post e o) := by
    apply currentSavedRegsKeptOffCore_of_savedRegsKeptOffCore
    cases caller? with
    | none => cases o <;> exact savedRegsKeptOffCore_refl e _
    | some tid => exact stageCallerReturnFor_savedRegsKeptOffCore o hInv (hFree tid rfl) hK hR
  have c3 : currentSavedRegsKeptOffCore e (Architecture.stageCallerReturnFor caller? post e o)
      (PriorityInheritance.scheduleLocalSuccessorFrom caller?
        (Architecture.stageCallerReturnFor caller? post e o) e) := by
    refine currentSavedRegsKeptOffCore_of_current ?_ (uniq B) hSucc.currentKept
    unfold PriorityInheritance.scheduleLocalSuccessorFrom
    split
    · split
      · rename_i st'' hRs
        rw [handleRescheduleSgiOnCore_eq_state] at hRs
        cases hRs
        exact handleRescheduleOnCoreState_savedRegsKeptExcept _ e hStageInv
      · exact .refl _
    · exact .refl _
  have c4 := currentSavedRegsKeptOffCore_of_eq (e := e)
    (settleResidencyOnCore_savedRegs _ e hSuccInv)
  have c5 := currentSavedRegsKeptOffCore_of_current
    (activateThreadOnCore_savedRegsKeptExcept _ e hSettleInv)
    ((uniq Full).of_scheduler (activateThreadOnCore_scheduler _ e).symm) hAct.currentKept
  exact currentSavedRegsKeptOffCore_trans (currentSavedRegsKeptOffCore_trans
    (currentSavedRegsKeptOffCore_trans c2 c3 hSucc.currentKept) c4 hSettle.currentKept)
    c5 hAct.currentKept

section
/- The composites below read the bank match only through the lemmas above.
Sealing it keeps the elaborator from evaluating a whole entry's state while it
checks an expected type of the form `contextMatchesCurrentOnCore X d`. -/
attribute [local irreducible] contextMatchesCurrentOnCore

/-- **The syscall seam after the dispatch keeps every other core's bank match**,
from the dispatch's frames (`hDc`) and census (`hDS`): the commit tail makes no
thread current on another core, writes no other core's bank, and writes the
saved registers of no thread current on another core
(`syscallCommitTail_currentSavedRegsKeptOffCore`). -/
theorem syscallCommitTail_contextMatchesCurrentOffCore {e : CoreId} {base post : SystemState}
    (caller? : Option SeLe4n.ThreadId) (o : Architecture.SyscallOutcome)
    (hDc : stepCovers e base post) (hDS : savedRegsKeptOffCore e base post)
    (hInv : post.objects.invExt) (hRef : post.runQueueRefined)
    (hDU : post.currentDequeuedUnique)
    (hFree : ∀ tid, caller? = some tid → offCoreFree e base tid)
    (d : CoreId) (hd : d ≠ e) (h : contextMatchesCurrentOnCore base d) :
    contextMatchesCurrentOnCore (Architecture.clearPhysicalWrites
      (Architecture.clearIcacheMaintenance (activateThreadOnCore (settleResidencyOnCore
        (PriorityInheritance.scheduleLocalSuccessorFrom caller?
          (Architecture.stageCallerReturnFor caller? post e o) e) e) e))) d := by
  have hTail := stepCovers_trans (syscallCommitTail_stepCovers e caller? post o hInv)
    (activateThreadOnCore_stepCovers e _ (settleResidencyOnCore_preserves_objects_invExt e _
      (scheduleLocalSuccessorFrom_preserves_objects_invExt e caller? _
        (stageCallerReturnFor_stepCovers e caller? post o hInv).2)))
  have hCov := stepCovers_trans hDc hTail
  have hS := currentSavedRegsKeptOffCore_trans
    (currentSavedRegsKeptOffCore_of_savedRegsKeptOffCore hDS)
    (syscallCommitTail_currentSavedRegsKeptOffCore caller? o hInv hRef hDU hFree
      hDc.currentKept hDc.residentKept) hTail.currentKept
  exact contextMatchesCurrentOnCore_clearLedgers'
    (contextMatchesCurrentOnCore_offCore hCov.currentKept hCov.banksKept hS d hd h)

/-- WS-ZA ZA6.28: **the syscall seam keeps every other core's bank match.**  It
makes no thread current on another core and writes no other core's bank
(`syscallDispatchCrossCoreStep_stepCovers`'s frames), and it writes the saved
registers of no thread current on another core: the dispatch's census
(`syscallDispatchFromAbi_savedRegsKeptOffCore`) and the commit tail's
(`syscallCommitTail_currentSavedRegsKeptOffCore`). -/
theorem syscallDispatchCrossCoreStep_contextMatchesCurrentOffCore {ctx : LabelingContext}
    {e : CoreId} {syscallId : UInt32}
    {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64} {S : SystemState}
    (E : EntryPremises S) (hRT : S.residentsHaveTcbs) (hN : S.currentNotResidentElsewhere)
    (hB : finalisingDeleteBundle S) (hBNR : S.blockedNotResident) (hYA : S.yieldLinksAgree)
    (hYN : S.yieldLinkedNotResident) (hPlaced : placedThreadsHaveTcbs S)
    (hAwayCur : ∀ t, S.scheduler.currentOnCore e = some t → ∀ c, S.queuedOn c t = false)
    (d : CoreId) (hd : d ≠ e) (h : contextMatchesCurrentOnCore S d) :
    contextMatchesCurrentOnCore (syscallDispatchCrossCoreStep ctx e syscallId
      x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 S).2 d := by
  have hU := currentsUnique_of_dequeuedUnique E.dequeued
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 S
  obtain ⟨hDc, hDInv⟩ := syscallDispatchFromAbi_stepCovers E.objInv hB hPlaced hAwayCur hD
  have A := syscallDispatchFromAbi_runQueueEntryStage E hD
  have hL := A.1.links E.objInv E.refined
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  exact syscallCommitTail_contextMatchesCurrentOffCore _ outcome hDc
    (syscallDispatchFromAbi_savedRegsKeptOffCore E hRT hN hB hBNR hYA hYN hPlaced hAwayCur hD)
    hDInv hL.2 (A.2 E.objInv E.refined hL.2 E.dequeued)
    (fun _ hCur => offCoreFree_of_current hCur hU hN) d hd h

/-- The syscall entry's save keeps every other core's bank match. -/
theorem saveCapturedSyscallFrame_contextMatchesCurrentOffCore (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt)
    (hU : currentsUnique st) (hN : st.currentNotResidentElsewhere) (d : CoreId) (hd : d ≠ c)
    (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore (Architecture.saveCapturedSyscallFrame st c frame) d := by
  cases frame with
  | none => exact h
  | some ic => exact saveTrapThenVacated_contextMatchesCurrentOnCore_offCore st c _ _ hInv hU hN d hd h

/-- WS-ZA ZA6.28: **the syscall entry keeps every other core's bank match.**  The
trap-frame save writes the executing core's bank, its current thread's saved
registers and a vacated core's resident's, none of them current on another core
(`saveTrapThenVacated_contextMatchesCurrentOnCore_offCore`); the IPC-buffer words
and their clear write neither; and the seam keeps the match
(`syscallDispatchCrossCoreStep_contextMatchesCurrentOffCore`), its premises
carried from the entry's state across the save and the words, which change no
IPC state, no yield link, no current slot and no residency record.  The
dispatch's coverage reads its other premises at the state the dispatch runs
from, as the sister carries do
(`syscallDispatchEntryState_preserves_currentNotResidentElsewhere`). -/
theorem syscallDispatchEntryState_preserves_contextMatchesCurrentOffCore (ctx : LabelingContext)
    (e : CoreId) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (E : EntryPremises st)
    (hB : finalisingDeleteBundle (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hPlaced : placedThreadsHaveTcbs (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hAwayCur : ∀ t, (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler.currentOnCore e = some t →
      ∀ c, (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n).queuedOn c t = false)
    (hC : st.currentNotResidentElsewhere) (hRT : st.residentsHaveTcbs)
    (hBNR : st.blockedNotResident) (hYA : st.yieldLinksAgree) (hYN : st.yieldLinkedNotResident)
    (d : CoreId) (hd : d ≠ e) (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2) d := by
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
  have hS0 : (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler = st.scheduler := by
    rw [Architecture.IpcBufferRead.syncUserWords_scheduler, saveCapturedSyscallFrame_scheduler]
  have hM0 : (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n).machine.residentCode =
        st.machine.residentCode := by
    rw [syncUserWords_residentCode, saveCapturedSyscallFrame_residentCode]
  have hU0 := currentsUnique_of_dequeuedUnique E.dequeued
  have hSave := saveCapturedSyscallFrame_contextMatchesCurrentOffCore st e frame E.objInv hU0 hC d hd h
  have hBNR' := BlockedNotResident.of_frame hBNR
    (fun d' tid hR => by
      simp only [MachineState.residentOnCore] at hR ⊢; rw [← hM0]; exact hR)
    (fun tid t' hT => by
      obtain ⟨t, hT0, hI, -⟩ := (hF E.objInv).2.2.1 tid t' hT
      exact ⟨t, hT0, hI⟩)
  refine syncUserWords_contextMatchesCurrentOnCore _ ByteArray.empty 0 d ?_
  exact syscallDispatchCrossCoreStep_contextMatchesCurrentOffCore (E.of_ipcFrame hS hF)
    (ResidentsHaveTcbs.of_kept hRT hM0 ((tcbsKept_saveCapturedSyscallFrame st e frame
      E.objInv).trans (tcbsKept.of_objects_eq
        (Architecture.IpcBufferRead.syncUserWords_objects _ bytes n))))
    (CurrentNotResidentElsewhere.of_frame hC hS0 hM0) hB hBNR'
    (hS.entry.yieldLinksAgree E.objInv E.refined hYA)
    (yieldLinkedNotResident_of_live hYN (hS.entry.1.live E.objInv E.refined)
      (currentsRecordUnlinked_of_scheduler_eq hS0))
    hPlaced hAwayCur d hd (syncUserWords_contextMatchesCurrentOnCore _ bytes n d hSave)

/-! ## The other entries -/

/-- **An entry's settle and activation keep every other core's bank match**,
from the step before them: a step that makes no thread current on another core,
writes no other core's bank and writes the saved registers of no thread current
on another core, followed by the residency settle (no saved register) and the
activation (the executing core's current thread alone, current nowhere else). -/
theorem settleThenActivateOnCore_contextMatchesCurrentOffCore {e : CoreId} {base M : SystemState}
    (hCov : stepCovers e base M) (hS : currentSavedRegsKeptOffCore e base M)
    (hInv : M.objects.invExt)
    (hU : currentsUnique (activateThreadOnCore (settleResidencyOnCore M e) e))
    (d : CoreId) (hd : d ≠ e) (h : contextMatchesCurrentOnCore base d) :
    contextMatchesCurrentOnCore (activateThreadOnCore (settleResidencyOnCore M e) e) d := by
  have hSettle := settleResidencyOnCore_stepCovers e M hInv
  have hSettleInv := settleResidencyOnCore_preserves_objects_invExt e M hInv
  have hAct := activateThreadOnCore_stepCovers e _ hSettleInv
  have hAll := stepCovers_trans (stepCovers_trans hCov hSettle) hAct
  have hS' := currentSavedRegsKeptOffCore_trans (currentSavedRegsKeptOffCore_trans hS
    (currentSavedRegsKeptOffCore_of_eq (settleResidencyOnCore_savedRegs M e hInv))
    hSettle.currentKept)
    (currentSavedRegsKeptOffCore_of_current (activateThreadOnCore_savedRegsKeptExcept _ e hSettleInv)
      (hU.of_scheduler (activateThreadOnCore_scheduler _ e).symm) hAct.currentKept)
    hAct.currentKept
  exact contextMatchesCurrentOnCore_offCore hAll.currentKept hAll.banksKept hS' d hd h

/-- The entry's trap-frame save keeps every other core's bank match. -/
theorem saveCapturedTrapFrame_contextMatchesCurrentOffCore (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt)
    (hU : currentsUnique st) (hN : st.currentNotResidentElsewhere) (d : CoreId) (hd : d ≠ c)
    (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore (Architecture.saveCapturedTrapFrame st c frame) d := by
  cases frame with
  | none => exact h
  | some ic => exact saveTrapThenVacated_contextMatchesCurrentOnCore_offCore st c _ _ hInv hU hN d hd h

/-- The reschedule step makes no thread current on another core, writes no other
core's bank, and writes the saved registers of the executing core's current
thread alone, which no other core runs. -/
theorem perCoreRescheduleStep_offCoreFrames (S : SystemState) (coreId : UInt64)
    (hlt : coreId.toNat < Concurrency.numCores) (hInv : S.objects.invExt)
    (hU : currentsUnique S) :
    stepCovers ⟨coreId.toNat, hlt⟩ S (perCoreRescheduleStep S coreId) ∧
      currentSavedRegsKeptOffCore ⟨coreId.toNat, hlt⟩ S (perCoreRescheduleStep S coreId) ∧
      (perCoreRescheduleStep S coreId).objects.invExt := by
  unfold perCoreRescheduleStep
  rw [dif_pos hlt]
  split
  · rename_i st' hR
    have hC := handleRescheduleSgiOnCore_stepCovers _ S st' hInv hR
    refine ⟨hC, currentSavedRegsKeptOffCore_of_current ?_ hU hC.currentKept,
      handleRescheduleSgiOnCore_preserves_objects_invExt _ _ st' hInv hR⟩
    rw [handleRescheduleSgiOnCore_eq_state] at hR
    cases hR
    exact handleRescheduleOnCoreState_savedRegsKeptExcept S _ hInv
  · exact ⟨stepCovers_refl _ S, currentSavedRegsKeptOffCore_refl _ S, hInv⟩

/-- WS-ZA ZA6.28: **the reschedule entry keeps every other core's bank match**
(the secondary core's first entry is this one): the save, the reschedule step
(`perCoreRescheduleStep_offCoreFrames`), the settle and the activation. -/
theorem perCoreRescheduleEntryState_preserves_contextMatchesCurrentOffCore (coreId : UInt64)
    (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hD : st.currentDequeuedUnique)
    (hN : st.currentNotResidentElsewhere) (d : CoreId) (hd : d ≠ c)
    (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) d := by
  have St := perCoreRescheduleEntryState_runQueueEntryStage coreId frame st
  have hUf := currentsUnique_of_dequeuedUnique (St.2 hInv hR (St.1.links hInv hR).2 hD)
  have hU0 := currentsUnique_of_dequeuedUnique hD
  obtain ⟨hlt, rfl⟩ := coreIdOfUInt64?_some hc
  simp only [activateThreadAt, PriorityInheritance.settleResidencyAt,
    Concurrency.saveCapturedTrapFrameAt, hc, rescheduleBracket_run] at hUf ⊢
  have hSv := saveCapturedTrapFrame_preserves_objects_invExt st ⟨coreId.toNat, hlt⟩ frame hInv
  have hSc := saveCapturedTrapFrame_contextMatchesCurrentOffCore st _ frame hInv hU0 hN d hd h
  have hUS := hU0.of_scheduler (saveCapturedTrapFrame_scheduler st ⟨coreId.toNat, hlt⟩ frame)
  generalize Architecture.saveCapturedTrapFrame st ⟨coreId.toNat, hlt⟩ frame = S at hSv hSc hUS hUf
  obtain ⟨hCov, hS, hI⟩ := perCoreRescheduleStep_offCoreFrames S coreId hlt hSv hUS
  exact contextMatchesCurrentOnCore_clearLedgers
    (settleThenActivateOnCore_contextMatchesCurrentOffCore hCov hS hI
      (hUf.of_scheduler (by simp [Architecture.clearIcacheMaintenance,
        Architecture.clearPhysicalWrites])) d hd hSc)

/-- WS-ZA ZA6.32: the interrupt step's off-core frames: it covers its reads
and writes, writes no saved register, and keeps the store well formed. -/
theorem interruptEntryStep_offCoreFrames (S : SystemState) (coreId intId : UInt64)
    (hlt : coreId.toNat < Concurrency.numCores) (hInv : S.objects.invExt) :
    stepCovers ⟨coreId.toNat, hlt⟩ S (interruptEntryStep S coreId intId) ∧
      currentSavedRegsKeptOffCore ⟨coreId.toNat, hlt⟩ S (interruptEntryStep S coreId intId) ∧
      (interruptEntryStep S coreId intId).objects.invExt :=
  have hW := interruptEntryStep_savedRegsUnwritten S coreId intId hInv
  ⟨interruptEntryStep_stepCovers _ S coreId intId hInv,
    currentSavedRegsKeptOffCore_of_kept hW.1 (fun _ h => h.elim), hW.2⟩

/-- WS-ZA ZA6.32: **the interrupt entry keeps every other core's bank match**:
the save, the interrupt step (`interruptEntryStep_offCoreFrames`), the settle
and the activation. -/
theorem interruptEntryState_preserves_contextMatchesCurrentOffCore (coreId intId : UInt64)
    (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (E : EntryPremises st) (hN : st.currentNotResidentElsewhere) (d : CoreId) (hd : d ≠ c)
    (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId intId)
        coreId) coreId))) d := by
  have St := interruptEntryState_runQueueEntryStage coreId intId frame st E
  have hUf := currentsUnique_of_dequeuedUnique (St.2 E.objInv E.refined
    (St.1.links E.objInv E.refined).2 E.dequeued)
  have hU0 := currentsUnique_of_dequeuedUnique E.dequeued
  obtain ⟨hlt, rfl⟩ := coreIdOfUInt64?_some hc
  simp only [activateThreadAt, PriorityInheritance.settleResidencyAt,
    Concurrency.saveCapturedTrapFrameAt, hc] at hUf ⊢
  have hSv := saveCapturedTrapFrame_preserves_objects_invExt st ⟨coreId.toNat, hlt⟩ frame E.objInv
  have hSc := saveCapturedTrapFrame_contextMatchesCurrentOffCore st _ frame E.objInv hU0 hN d hd h
  generalize Architecture.saveCapturedTrapFrame st ⟨coreId.toNat, hlt⟩ frame = S at hSv hSc hUf
  obtain ⟨hCov, hS, hI⟩ := interruptEntryStep_offCoreFrames S coreId intId hlt hSv
  exact contextMatchesCurrentOnCore_clearLedgers
    (settleThenActivateOnCore_contextMatchesCurrentOffCore hCov hS hI
      (hUf.of_scheduler (by simp [Architecture.clearIcacheMaintenance,
        Architecture.clearPhysicalWrites])) d hd hSc)

/-- WS-ZA ZA6.32: **the interrupt step keeps every core's bank match**, the
executing core's included.  Its frames hold whichever core is named the
executing one (`interruptEntryStep_offCoreFrames` is stated at any core), so
name one other than `d`: the step makes no thread current, writes no bank and
writes no saved register. -/
theorem interruptEntryStep_contextMatchesCurrentOnCore (S : SystemState) (coreId intId : UInt64)
    (hInv : S.objects.invExt) (d : CoreId) (h : contextMatchesCurrentOnCore S d) :
    contextMatchesCurrentOnCore (interruptEntryStep S coreId intId) d := by
  obtain ⟨e, he⟩ := exists_core_ne d
  have hC := interruptEntryStep_stepCovers e S coreId intId hInv
  have hW := interruptEntryStep_savedRegsUnwritten S coreId intId hInv
  exact contextMatchesCurrentOnCore_offCore hC.currentKept hC.banksKept
    (currentSavedRegsKeptOffCore_of_kept hW.1 (fun _ h => h.elim)) d (Ne.symm he) h

/-- WS-ZA ZA6.32: **the interrupt entry keeps the executing core's bank its
current thread's context**: the save, the interrupt step
(`interruptEntryStep_contextMatchesCurrentOnCore`), the settle and the
activation. -/
theorem interruptEntryState_preserves_contextMatchesCurrentOnCore (coreId intId : UInt64)
    (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hInv : st.objects.invExt) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId intId)
        coreId) coreId))) c := by
  obtain ⟨hlt, rfl⟩ := coreIdOfUInt64?_some hc
  simp only [activateThreadAt, PriorityInheritance.settleResidencyAt,
    Concurrency.saveCapturedTrapFrameAt, hc]
  have hSv := saveCapturedTrapFrame_preserves_objects_invExt st ⟨coreId.toNat, hlt⟩ frame hInv
  have hSc := saveCapturedTrapFrame_preserves_contextMatchesCurrentOnCore st ⟨coreId.toNat, hlt⟩
    frame hInv h
  exact settleThenActivateOnCore_preserves_contextMatchesCurrentOnCore _ _
    (interruptEntryStep_preserves_objects_invExt _ coreId intId hSv)
    (interruptEntryStep_contextMatchesCurrentOnCore _ coreId intId hSv _ hSc)

/-- **The FP/SIMD switch keeps every core's bank match**: it writes a thread's
FP/SIMD context and the core's FP owner, never a saved register, a current slot
or a bank. -/
theorem fpAccessOnCore_contextMatchesCurrentOnCore_any (st : SystemState) (c : CoreId)
    (live : Option FpContext) (hInv : st.objects.invExt) (d : CoreId)
    (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore (Architecture.fpAccessOnCore st c live).2 d := by
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

/-- WS-ZA ZA6.28: **the FP/SIMD entry keeps every other core's bank match**: the
save, the FP/SIMD switch (`fpAccessOnCore_contextMatchesCurrentOnCore_any`), the
vacated core's dispatch (no saved register), the settle and the activation. -/
theorem fpAccessEntryState_preserves_contextMatchesCurrentOffCore (coreId : UInt64)
    (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext) (st : SystemState)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hD : st.currentDequeuedUnique)
    (hN : st.currentNotResidentElsewhere) (d : CoreId) (hd : d ≠ c)
    (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore (activateThreadAt (PriorityInheritance.settleResidencyAt
      (fpAccessEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2
        coreId) coreId) d := by
  have St := fpAccessEntryState_runQueueEntryStage coreId frame live st
  have hUf := currentsUnique_of_dequeuedUnique (St.2 hInv hR (St.1.links hInv hR).2 hD)
  have hU0 := currentsUnique_of_dequeuedUnique hD
  obtain ⟨hlt, rfl⟩ := coreIdOfUInt64?_some hc
  simp only [activateThreadAt, PriorityInheritance.settleResidencyAt,
    Concurrency.saveCapturedTrapFrameAt, fpAccessEntryStep, hc] at hUf ⊢
  have hSv := saveCapturedTrapFrame_preserves_objects_invExt st ⟨coreId.toNat, hlt⟩ frame hInv
  have hSc := saveCapturedTrapFrame_contextMatchesCurrentOffCore st _ frame hInv hU0 hN d hd h
  generalize Architecture.saveCapturedTrapFrame st ⟨coreId.toNat, hlt⟩ frame = S at hSv hSc hUf
  have hFI := fpAccessOnCore_preserves_objects_invExt S ⟨coreId.toNat, hlt⟩ live hSv
  have hFc := fpAccessOnCore_contextMatchesCurrentOnCore_any S ⟨coreId.toNat, hlt⟩ live hSv d hSc
  generalize (Architecture.fpAccessOnCore S ⟨coreId.toNat, hlt⟩ live).2 = F at hFI hFc hUf
  exact settleThenActivateOnCore_contextMatchesCurrentOffCore
    (dispatchVacatedCore_stepCovers _ F hFI)
    (currentSavedRegsKeptOffCore_of_eq (dispatchVacatedCore_savedRegs F _ hFI))
    (dispatchVacatedCore_preserves_objects_invExt _ F hFI) hUf d hd hFc

/-- **The shared fault delivery writes the saved registers of no thread current
on another core**: a vacated core's dispatch writes none; an idle thread's trap
commits nothing; a delivery writes the faulting thread, the executing core's
current thread, and the woken handler, the head of an endpoint's receive queue,
blocked at the entry's start (`faultDeliverOnCoreChecked_savedRegsWrittenFree`),
and its successor saves nobody, the delivery having vacated the core. -/
theorem faultEntryDeliver_currentSavedRegsKeptOffCore (lctx : LabelingContext)
    (st : SystemState) (f : Fault) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (c : CoreId) (E : EntryPremises st)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (hN : st.currentNotResidentElsewhere) :
    currentSavedRegsKeptOffCore c st (faultEntryDeliver lctx st f ectx w c).2 := by
  have hInv := E.objInv
  have hU := currentsUnique_of_dequeuedUnique E.dequeued
  unfold faultEntryDeliver
  split
  · exact currentSavedRegsKeptOffCore_of_eq (dispatchVacatedCore_savedRegs st c hInv)
  · rename_i tid hCur
    split
    · exact currentSavedRegsKeptOffCore_refl c st
    · dsimp only
      obtain ⟨hDc, hDI⟩ := faultDeliveredState_stepCovers c (lctx := lctx) (f := f)
        (ectx := ectx) (w := w) (c := c) (tid := tid) hInv
      have hV := faultDeliveredState_vacates lctx st f ectx w c tid hInv hCur
      have hFr : offCoreFree c st tid := offCoreFree_of_current hCur hU hN
      have iW : (writeFaultRegistersToTcb st tid w).objects.invExt := by
        unfold writeFaultRegistersToTcb; exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv
      have hW : savedRegsKeptExcept (· = tid) st (writeFaultRegistersToTcb st tid w) := by
        unfold writeFaultRegistersToTcb; exact .updateTcb_written _ _ _ hInv rfl
      have hD1 : savedRegsKeptOffCore c st (faultDeliveredState lctx st f ectx w c tid) := by
        refine savedRegsWrittenFree.census (base := st) ?_ hDc.currentKept hDc.residentKept
        unfold faultDeliveredState
        dsimp only
        refine (savedRegsWrittenFree.of_kept hW fun _ e => e ▸ hFr).trans
          (faultDeliverOnCoreChecked_savedRegsWrittenFree iW fun ep t ht => ?_)
        unfold writeFaultRegistersToTcb at ht
        rw [updateTcb_getEndpoint? hInv] at ht
        exact offCoreFree_of_receiveHead E.dequeued E.queueHeads hRT hBNR ht
      have hSucc := scheduleLocalSuccessorFrom_stepCovers c (some tid) _ hDI
      refine currentSavedRegsKeptOffCore_trans
        (currentSavedRegsKeptOffCore_of_savedRegsKeptOffCore hD1) ?_ hSucc.currentKept
      refine currentSavedRegsKeptOffCore_of_eq fun t => ?_
      generalize faultDeliveredState lctx st f ectx w c tid = D at hDI hV ⊢
      unfold PriorityInheritance.scheduleLocalSuccessorFrom
      split
      · split
        · rename_i st'' hR
          rw [handleRescheduleSgiOnCore_eq_state] at hR
          cases hR
          exact handleRescheduleOnCoreState_savedRegsKeptExcept D c hDI t (by rw [hV]; simp)
        · rfl
      · rfl

/-- The entry's premises carry across the trap-frame save, which writes saved
registers and a bank alone. -/
theorem saveCapturedTrapFrame_carriesPremises (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) (E : EntryPremises st)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (hN : st.currentNotResidentElsewhere) :
    EntryPremises (Architecture.saveCapturedTrapFrame st c frame) ∧
      (Architecture.saveCapturedTrapFrame st c frame).residentsHaveTcbs ∧
      (Architecture.saveCapturedTrapFrame st c frame).blockedNotResident ∧
      (Architecture.saveCapturedTrapFrame st c frame).currentNotResidentElsewhere := by
  have hF := saveCapturedTrapFrame_ipcFrame st c frame
  have hM := saveCapturedTrapFrame_residentCode st c frame
  have hT : tcbsKept st (Architecture.saveCapturedTrapFrame st c frame) := by
    cases frame with
    | none => exact tcbsKept.refl st
    | some ic =>
      exact (tcbsKept_saveTrapFrameOnCore st _ _ E.objInv).trans
        (tcbsKept_saveVacatedFrameOnCore _ _ _ _
          (Architecture.saveTrapFrameOnCore_preserves_objects_invExt st _ _ E.objInv))
  refine ⟨E.of_ipcFrame (saveCapturedTrapFrame_runQueueStage st c frame) hF,
    ResidentsHaveTcbs.of_kept hRT hM hT, BlockedNotResident.of_frame hBNR
      (fun d' tid hR => by simp only [MachineState.residentOnCore] at hR ⊢; rw [← hM]; exact hR)
      (fun tid t' hT' => by
        obtain ⟨t, hT0, hI, -⟩ := (hF E.objInv).2.2.1 tid t' hT'
        exact ⟨t, hT0, hI⟩),
    CurrentNotResidentElsewhere.of_frame hN (saveCapturedTrapFrame_scheduler st c frame) hM⟩

/-- The fault step makes no thread current on another core, writes no other
core's bank, and writes the saved registers of no thread current on another
core (`faultEntryDeliver_currentSavedRegsKeptOffCore`). -/
theorem faultEntryStep_offCoreFrames (lctx : LabelingContext) (S : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hlt : coreId.toNat < Concurrency.numCores) (E : EntryPremises S)
    (hRT : S.residentsHaveTcbs) (hBNR : S.blockedNotResident)
    (hN : S.currentNotResidentElsewhere) :
    stepCovers ⟨coreId.toNat, hlt⟩ S (faultEntryStep lctx S ectx w coreId).2 ∧
      currentSavedRegsKeptOffCore ⟨coreId.toNat, hlt⟩ S (faultEntryStep lctx S ectx w coreId).2 ∧
      (faultEntryStep lctx S ectx w coreId).2.objects.invExt := by
  unfold faultEntryStep
  rw [dif_pos hlt]
  split
  · split
    · exact ⟨stepCovers_refl _ S, currentSavedRegsKeptOffCore_refl _ S, E.objInv⟩
    · exact ⟨faultEntryDeliver_stepCovers lctx S _ ectx w _ E.objInv,
        faultEntryDeliver_currentSavedRegsKeptOffCore lctx S _ ectx w _ E hRT hBNR hN,
        faultEntryDeliver_preserves_objects_invExt lctx S _ ectx w _ E.objInv⟩
  · exact ⟨stepCovers_refl _ S, currentSavedRegsKeptOffCore_refl _ S, E.objInv⟩

/-- WS-ZA ZA6.28: **the fault entry keeps every other core's bank match**: the
save, the fault step (`faultEntryStep_offCoreFrames`), the settle and the
activation. -/
theorem faultEntryState_preserves_contextMatchesCurrentOffCore (lctx : LabelingContext)
    (coreId : UInt64) (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (hN : st.currentNotResidentElsewhere) (d : CoreId) (hd : d ≠ c)
    (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx (Concurrency.saveCapturedTrapFrameAt st coreId frame) ectx w
          coreId).2 coreId) coreId))) d := by
  obtain ⟨hlt, rfl⟩ := coreIdOfUInt64?_some hc
  simp only [activateThreadAt, PriorityInheritance.settleResidencyAt,
    Concurrency.saveCapturedTrapFrameAt, hc]
  have hSc := saveCapturedTrapFrame_contextMatchesCurrentOffCore st _ frame E.objInv
    (currentsUnique_of_dequeuedUnique E.dequeued) hN d hd h
  obtain ⟨ES, hRTS, hBS, hNS⟩ := saveCapturedTrapFrame_carriesPremises st ⟨coreId.toNat, hlt⟩
    frame E hRT hBNR hN
  generalize Architecture.saveCapturedTrapFrame st ⟨coreId.toNat, hlt⟩ frame = S at hSc ES hRTS hBS hNS
  have Stg := (faultEntryStep_runQueueEntryStage lctx S ectx w coreId ES).trans
    (settleThenActivateOnCore_runQueueEntryStage _ ⟨coreId.toNat, hlt⟩)
  have hU := currentsUnique_of_dequeuedUnique
    (Stg.2 ES.objInv ES.refined (Stg.1.links ES.objInv ES.refined).2 ES.dequeued)
  obtain ⟨hCov, hS, hI⟩ := faultEntryStep_offCoreFrames lctx S ectx w coreId hlt ES hRTS hBS hNS
  exact contextMatchesCurrentOnCore_clearLedgers
    (settleThenActivateOnCore_contextMatchesCurrentOffCore hCov hS hI hU d hd hSc)

/-- The entry's premises carry across the syscall entry's save. -/
theorem saveCapturedSyscallFrame_carriesPremises (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) (E : EntryPremises st)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (hN : st.currentNotResidentElsewhere) :
    EntryPremises (Architecture.saveCapturedSyscallFrame st c frame) ∧
      (Architecture.saveCapturedSyscallFrame st c frame).residentsHaveTcbs ∧
      (Architecture.saveCapturedSyscallFrame st c frame).blockedNotResident ∧
      (Architecture.saveCapturedSyscallFrame st c frame).currentNotResidentElsewhere := by
  have hF := saveCapturedSyscallFrame_ipcFrame st c frame
  have hM := saveCapturedSyscallFrame_residentCode st c frame
  refine ⟨E.of_ipcFrame (saveCapturedSyscallFrame_runQueueStage st c frame) hF,
    ResidentsHaveTcbs.of_kept hRT hM (tcbsKept_saveCapturedSyscallFrame st c frame E.objInv),
    BlockedNotResident.of_frame hBNR
      (fun d' tid hR => by simp only [MachineState.residentOnCore] at hR ⊢; rw [← hM]; exact hR)
      (fun tid t' hT' => by
        obtain ⟨t, hT0, hI, -⟩ := (hF E.objInv).2.2.1 tid t' hT'
        exact ⟨t, hT0, hI⟩),
    CurrentNotResidentElsewhere.of_frame hN (saveCapturedSyscallFrame_scheduler st c frame) hM⟩

/-- The unknown-syscall step is the shared fault delivery
(`faultEntryDeliver_currentSavedRegsKeptOffCore`), or nothing. -/
theorem unknownSyscallEntryStep_offCoreFrames (lctx : LabelingContext) (S : SystemState)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hlt : coreId.toNat < Concurrency.numCores) (E : EntryPremises S)
    (hRT : S.residentsHaveTcbs) (hBNR : S.blockedNotResident)
    (hN : S.currentNotResidentElsewhere) :
    stepCovers ⟨coreId.toNat, hlt⟩ S (unknownSyscallEntryStep lctx S ectx w coreId).2 ∧
      currentSavedRegsKeptOffCore ⟨coreId.toNat, hlt⟩ S
        (unknownSyscallEntryStep lctx S ectx w coreId).2 ∧
      (unknownSyscallEntryStep lctx S ectx w coreId).2.objects.invExt := by
  unfold unknownSyscallEntryStep
  rw [dif_pos hlt]
  split
  · exact ⟨faultEntryDeliver_stepCovers lctx S _ ectx w _ E.objInv,
      faultEntryDeliver_currentSavedRegsKeptOffCore lctx S _ ectx w _ E hRT hBNR hN,
      faultEntryDeliver_preserves_objects_invExt lctx S _ ectx w _ E.objInv⟩
  · exact ⟨stepCovers_refl _ S, currentSavedRegsKeptOffCore_refl _ S, E.objInv⟩

/-- WS-ZA ZA6.28: **the unknown-syscall entry keeps every other core's bank
match**: the syscall entry's save, the shared fault delivery
(`unknownSyscallEntryStep_offCoreFrames`), the settle and the activation. -/
theorem unknownSyscallEntryState_preserves_contextMatchesCurrentOffCore
    (lctx : LabelingContext) (coreId : UInt64) (c : CoreId)
    (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (E : EntryPremises st)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (hN : st.currentNotResidentElsewhere) (d : CoreId) (hd : d ≠ c)
    (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx (Concurrency.saveCapturedSyscallFrameAt st coreId frame)
          ectx w coreId).2 coreId) coreId))) d := by
  obtain ⟨hlt, rfl⟩ := coreIdOfUInt64?_some hc
  simp only [activateThreadAt, PriorityInheritance.settleResidencyAt,
    Concurrency.saveCapturedSyscallFrameAt, hc]
  have hSc := saveCapturedSyscallFrame_contextMatchesCurrentOffCore st _ frame E.objInv
    (currentsUnique_of_dequeuedUnique E.dequeued) hN d hd h
  obtain ⟨ES, hRTS, hBS, hNS⟩ := saveCapturedSyscallFrame_carriesPremises st ⟨coreId.toNat, hlt⟩
    frame E hRT hBNR hN
  generalize Architecture.saveCapturedSyscallFrame st ⟨coreId.toNat, hlt⟩ frame = S
    at hSc ES hRTS hBS hNS
  have Stg := (unknownSyscallEntryStep_runQueueEntryStage lctx S ectx w coreId ES).trans
    (settleThenActivateOnCore_runQueueEntryStage _ ⟨coreId.toNat, hlt⟩)
  have hU := currentsUnique_of_dequeuedUnique
    (Stg.2 ES.objInv ES.refined (Stg.1.links ES.objInv ES.refined).2 ES.dequeued)
  obtain ⟨hCov, hS, hI⟩ :=
    unknownSyscallEntryStep_offCoreFrames lctx S ectx w coreId hlt ES hRTS hBS hNS
  exact contextMatchesCurrentOnCore_clearLedgers
    (settleThenActivateOnCore_contextMatchesCurrentOffCore hCov hS hI hU d hd hSc)

end

end SeLe4n.Kernel
