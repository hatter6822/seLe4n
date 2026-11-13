/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.ExecutingBankDispatch

/-!
# The executing core's bank match after a syscall

The syscall entry's save makes the executing core's bank its current thread's
context (`syscallEntrySaved_contextMatchesCurrentOnCore`), and the argument
spill keeps it (`syscallEntrySpill_contextMatchesCurrentOnCore_iff`).  From
there:

* the dispatch keeps the agreement `bankAgree` for the caller
  (`syscallEntryChecked_bankAgree`), so the commit's staging of a returning
  caller makes it the match again, and a caller that does not return is current
  nowhere (`blockedCurrentNowhere`), so the agreement is the match;
* a delivered capability fault vacates the core, and a refusal writes no
  object, slot or bank;
* the commit tail's scheduling point, residency settle and activation keep the
  match.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-ZA ZA6.28: **the syscall dispatch leaves the executing core's bank
matching after the commit's staging**: from a match before the dispatch and
after the argument spill, each of the dispatch's arms keeps it (see the module
docstring). -/
theorem syscallDispatchFromAbi_stagedContextMatches {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (E : EntryPremises st) (hRT : st.residentsHaveTcbs)
    (hB : finalisingDeleteBundle st) (hBNR : st.blockedNotResident) (hYA : st.yieldLinksAgree)
    (hYN : st.yieldLinkedNotResident) (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (hM : contextMatchesCurrentOnCore st e)
    (hSpill : ∀ tid, st.scheduler.currentOnCore e = some tid → contextMatchesCurrentOnCore
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) e)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st = .ok (outcome, st')) :
    contextMatchesCurrentOnCore
      (Architecture.stageCallerReturnFor (st.scheduler.currentOnCore e) st' e outcome) e := by
  have hInv := E.objInv
  obtain ⟨hC, hDInv⟩ := syscallDispatchFromAbi_stepCovers hInv hB hPlaced hAwayCur h
  have A := syscallDispatchFromAbi_runQueueEntryStage E h
  have hDU := A.2 E.objInv E.refined (A.1.links E.objInv E.refined).2 E.dequeued
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact contextMatchesCurrentOnCore_stageCallerReturnFor _ _ hInv hM
  rename_i tid hCur
  rw [hCur]
  split at h
  · cases h; exact contextMatchesCurrentOnCore_stageCallerReturnFor _ _ hInv hM
  rename_i hIdle
  have hNI : isIdleThreadId tid = false := by simpa using hIdle
  have hSp := hSpill tid hCur
  have hEq := Platform.FFI.writeFfiRegistersToTcb_eq_updateTcb st tid syscallId x0 x1 x2 x3 x4 x5
  have iW : (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5).objects.invExt
    := by rw [hEq]; exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv
  dsimp only at h
  split at h
  · split at h
    · rename_i fault _
      cases h
      refine contextMatchesCurrentOnCore_stageCallerReturnFor _ _ hDInv ?_
      have hW := writeFfiRegistersToTcb_keyFrame st tid syscallId x0 x1 x2 x3 x4 x5 hInv
      have hF := writeFaultRegistersToTcb_keyFrame _ tid
        (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr spEl0 x30) hW.2.2
      have hO := stepCovers_trans (stepCovers_trans (e := otherCore e) hW.stepCovers
        hF.stepCovers) (faultDeliverOnCoreChecked_stepCovers (otherCore e) (lctx := ctx)
          (tid := tid) (f := fault) (c := e) (ctx := Architecture.faultContextOfThread
            (writeFaultRegistersToTcb (Platform.FFI.writeFfiRegistersToTcb st tid syscallId
              x0 x1 x2 x3 x4 x5) tid (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5
                ipcBufferAddr spEl0 x30)) tid (Platform.FFI.svcFaultIP elr) spsr) hF.2.2).1
      unfold Platform.FFI.deliverSyscallCapFault
      dsimp only
      generalize hX : (faultDeliverOnCoreChecked _ _ _ _ _ _).1 = X at hO ⊢
      have hV : X.scheduler.currentOnCore e = none := by
        cases hP : X.scheduler.currentOnCore e with
        | none => rfl
        | some t =>
          have hT := hO.currentKept e (ne_otherCore e) t hP
          rw [hCur] at hT; cases hT
          subst hX
          exact absurd hP (faultDeliverOnCoreChecked_leaves_thread_not_runnable _ _ tid _ _ e).2
      unfold contextMatchesCurrentOnCore; rw [hV]; trivial
    · cases h
      refine contextMatchesCurrentOnCore_stageCallerReturnFor _ _ hDInv ?_
      exact (contextMatchesCurrentOnCore_frame
        (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq, Architecture.recordErrorOverflow_scheduler])
        (by rw [Platform.FFI.recordSyscallRefusal_machine_eq, Architecture.recordErrorOverflow_machine])
        ((Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _).trans
          (Architecture.recordErrorOverflow_objects _ _ _))).mpr hSp
  · rename_i hE
    cases h
    have hB' := finalisingDeleteBundle_writeFfiRegistersToTcb tid syscallId x0 x1 x2 x3 x4 x5 hB
    have hPl : placedThreadsHaveTcbs
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
      rw [hEq]; exact placedThreadsHaveTcbs_updateTcb hInv hPlaced
    have hS : SystemState.RunQueueStage st
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
      rw [hEq]; exact SystemState.RunQueueStage.updateTcb _ _ (fun _ _ => rfl)
    have E1 := E.of_ipcFrame hS (by rw [hEq]; exact IpcFrame.updateTcb _ _ fun _ => rfl)
    have hC0 : (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5
        ).scheduler.currentOnCore e = some tid := by
      rw [Platform.FFI.writeFfiRegistersToTcb_scheduler]; exact hCur
    have hA := syscallEntryChecked_bankAgree E1 (fun t ht => by
        rw [hC0] at ht; cases ht; exact hNI)
      (by rw [hEq]; exact residentsHaveTcbs_updateTcb hInv hRT) hB'
      (by rw [hEq]; exact blockedNotResident_updateTcb hInv (fun _ => rfl) hBNR)
      (by
        rw [hEq]
        exact SystemState.yieldLinksAgree_of_kept
          (YieldLinksKept.updateTcb _ _ _ hInv fun _ => rfl) hYA)
      (by rw [hEq]; exact yieldLinkedNotResident_updateTcb hInv (fun _ => rfl) hYN)
      hPl hC0 hE (bankAgree_of_match hSp)
    refine contextMatchesCurrentOnCore_stageCallerReturnFor_of_bankAgree _ hDInv hA ?_
    intro hNot hCurT
    cases hT : st'.getTcb? tid with
    | none =>
      exact hNot _ (by unfold Platform.FFI.syscallReturnOutcome; simp only [hT]; rfl)
    | some tcb =>
      cases hb : Architecture.ipcStateBlocksReturn tcb.ipcState with
      | false =>
        exact hNot _ (by
          unfold Platform.FFI.syscallReturnOutcome
          simp only [hT, hb, Bool.false_eq_true, ↓reduceIte]; rfl)
      | true =>
        have hNe : tcb.ipcState ≠ .ready := fun hr => by
          rw [hr, Architecture.ipcStateBlocksReturn_ready] at hb; cases hb
        exact blockedCurrentNowhere_of_currentDequeuedUnique hDU tid tcb hT hNe e hCurT

/-- **The local scheduling point keeps the executing core's bank match**: it is
the reschedule handler or nothing. -/
theorem scheduleLocalSuccessorFrom_preserves_contextMatchesCurrentOnCore {e : CoreId}
    (caller? : Option SeLe4n.ThreadId) (post : SystemState) (hInv : post.objects.invExt)
    (h : contextMatchesCurrentOnCore post e) :
    contextMatchesCurrentOnCore (PriorityInheritance.scheduleLocalSuccessorFrom caller? post e) e
    := by
  unfold PriorityInheritance.scheduleLocalSuccessorFrom
  split
  · split
    · rename_i s hR
      exact handleRescheduleSgiOnCore_preserves_contextMatchesCurrentOnCore post e s hInv h hR
    · exact h
  · exact h

section
/- As in `OffCoreContextMatches`: the composites read the bank match only
through the lemmas above. -/
attribute [local irreducible] contextMatchesCurrentOnCore

/-- WS-ZA ZA6.28: **the syscall seam keeps the executing core's bank match**,
from a match before the dispatch and after the argument spill: the dispatch and
the commit's staging keep it (`syscallDispatchFromAbi_stagedContextMatches`),
and the local scheduling point, the residency settle, the activation and the
ledger clears keep it. -/
theorem syscallDispatchCrossCoreStep_contextMatchesCurrentOnCore {ctx : LabelingContext}
    {e : CoreId} {syscallId : UInt32}
    {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64} {S : SystemState}
    (E : EntryPremises S) (hRT : S.residentsHaveTcbs)
    (hB : finalisingDeleteBundle S) (hBNR : S.blockedNotResident) (hYA : S.yieldLinksAgree)
    (hYN : S.yieldLinkedNotResident) (hPlaced : placedThreadsHaveTcbs S)
    (hAwayCur : ∀ t, S.scheduler.currentOnCore e = some t → ∀ c, S.queuedOn c t = false)
    (hM : contextMatchesCurrentOnCore S e)
    (hSpill : ∀ tid, S.scheduler.currentOnCore e = some tid → contextMatchesCurrentOnCore
      (Platform.FFI.writeFfiRegistersToTcb S tid syscallId x0 x1 x2 x3 x4 x5) e) :
    contextMatchesCurrentOnCore (syscallDispatchCrossCoreStep ctx e syscallId
      x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 S).2 e := by
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 S
  have hDInv := (syscallDispatchFromAbi_stepCovers E.objInv hB hPlaced hAwayCur hD).2
  have hStage := syscallDispatchFromAbi_stagedContextMatches E hRT hB hBNR hYA hYN hPlaced
    hAwayCur hM hSpill hD
  have iStage := (stageCallerReturnFor_stepCovers e (S.scheduler.currentOnCore e) st' outcome
    hDInv).2
  have hSucc := scheduleLocalSuccessorFrom_preserves_contextMatchesCurrentOnCore
    (S.scheduler.currentOnCore e) _ iStage hStage
  have iSucc := scheduleLocalSuccessorFrom_preserves_objects_invExt e
    (S.scheduler.currentOnCore e) _ iStage
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  exact contextMatchesCurrentOnCore_clearLedgers'
    (activateThreadOnCore_preserves_contextMatchesCurrentOnCore _ e
      (settleResidencyOnCore_preserves_objects_invExt e _ iSucc)
      (settleResidencyOnCore_preserves_contextMatchesCurrentOnCore _ e iSucc hSucc))


/-- WS-ZA ZA6.28: **the syscall entry leaves the executing core's bank its
current thread's context.**  The entry's save of the admitted frame makes the
bank the caller's context (`syscallEntrySaved_contextMatchesCurrentOnCore`),
the IPC-buffer words write neither, the argument spill keeps the match
(`syscallEntrySpill_contextMatchesCurrentOnCore_iff`), and the seam keeps it
(`syscallDispatchCrossCoreStep_contextMatchesCurrentOnCore`), its premises
carried from the entry's state as the other cores' carry does
(`syscallDispatchEntryState_preserves_contextMatchesCurrentOffCore`).  With it,
every core's bank matches its current thread after the syscall entry. -/
theorem syscallDispatchEntryState_preserves_contextMatchesCurrentOnCore (ctx : LabelingContext)
    (e : CoreId) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext)
    (hAdm : syscallEntryContextOrFaulted frame = .ok trapped) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (E : EntryPremises st)
    (hB : finalisingDeleteBundle (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hPlaced : placedThreadsHaveTcbs (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hAwayCur : ∀ t, (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler.currentOnCore e = some t →
      ∀ c, (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n).queuedOn c t = false)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident) (hYA : st.yieldLinksAgree)
    (hYN : st.yieldLinkedNotResident) :
    contextMatchesCurrentOnCore (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2) e := by
  have hS := (saveCapturedSyscallFrame_runQueueStage st e frame).trans
    (SystemState.RunQueueStage.of_frame (Architecture.IpcBufferRead.syncUserWords_objects _ _ _)
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
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
  have hBNR' := BlockedNotResident.of_frame hBNR
    (fun d' tid hR => by
      simp only [MachineState.residentOnCore] at hR ⊢; rw [← hM0]; exact hR)
    (fun tid t' hT => by
      obtain ⟨t, hT0, hI, -⟩ := (hF E.objInv).2.2.1 tid t' hT
      exact ⟨t, hT0, hI⟩)
  have hM := syscallEntrySaved_contextMatchesCurrentOnCore hAdm st e bytes n E.objInv
  refine syncUserWords_contextMatchesCurrentOnCore _ ByteArray.empty 0 e ?_
  exact syscallDispatchCrossCoreStep_contextMatchesCurrentOnCore (E.of_ipcFrame hS hF)
    (ResidentsHaveTcbs.of_kept hRT hM0 ((tcbsKept_saveCapturedSyscallFrame st e frame
      E.objInv).trans (tcbsKept.of_objects_eq
        (Architecture.IpcBufferRead.syncUserWords_objects _ bytes n))))
    hB hBNR'
    (hS.entry.yieldLinksAgree E.objInv E.refined hYA)
    (yieldLinkedNotResident_of_live hYN (hS.entry.1.live E.objInv E.refined)
      (currentsRecordUnlinked_of_scheduler_eq hS0))
    hPlaced hAwayCur hM
    (fun tid hCur => (syscallEntrySpill_contextMatchesCurrentOnCore_iff hAdm st e bytes n
      E.objInv tid hCur e).mpr hM)


/-- WS-ZA ZA6.28: **after the syscall entry every core's bank is its current
thread's context**: the executing core's by the entry's save
(`syscallDispatchEntryState_preserves_contextMatchesCurrentOnCore`), every other
core's from its match before the entry
(`syscallDispatchEntryState_preserves_contextMatchesCurrentOffCore`). -/
theorem syscallDispatchEntryState_preserves_contextMatchesCurrentEveryCore
    (ctx : LabelingContext) (e : CoreId) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext)
    (hAdm : syscallEntryContextOrFaulted frame = .ok trapped) (bytes : ByteArray) (n : Nat)
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
    (h : ∀ d, d ≠ e → contextMatchesCurrentOnCore st d) (d : CoreId) :
    contextMatchesCurrentOnCore (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2) d := by
  by_cases hd : d = e
  · subst hd
    exact syscallDispatchEntryState_preserves_contextMatchesCurrentOnCore ctx d trapped frame
      hAdm bytes n st E hB hPlaced hAwayCur hRT hBNR hYA hYN
  · exact syscallDispatchEntryState_preserves_contextMatchesCurrentOffCore ctx e trapped frame
      bytes n st E hB hPlaced hAwayCur hC hRT hBNR hYA hYN d hd (h d hd)

end

end SeLe4n.Kernel
