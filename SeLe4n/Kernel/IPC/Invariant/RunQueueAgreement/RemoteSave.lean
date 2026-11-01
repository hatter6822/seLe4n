/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.EntryContextMatches

/-!
# The remote stall waits for the remote save

WS-ZA ZA6.11.  A commit that takes a thread off another core's current slot
leaves the thread's live registers in that core's bank: the core still runs it
at EL0, and `MachineState.residentOnCore` records it there.  seL4's
`remoteTCBStall` does not let the operation return until the remote core has
rescheduled, so the registers are in the TCB.  This kernel's stall
(`Concurrency.stallChangedCores`, the HAL's `remote_stall`) does the same in
three parts, and this module proves what the model reaches of each:

1. **The stall set.**  Under the kernel-entry lock, after the commit, the HAL
   stalls every other core whose committed thread is not the one it last
   decided to run (`Concurrency.stallsOn`).  `Concurrency.stallsOn_of_taken`: every core the commit took
   a thread off is stalled, given the HAL record names what the core runs.
2. **The target's save.**  The HAL samples the target's save epoch under the
   lock and the initiator returns to EL0 only once the target has completed a
   locked entry after it.  That entry runs from a state in which the target is
   still vacated and still holds the thread, or the thread's record was
   released by a final delete, whatever other cores committed in between
   (`keptOnCore_of_stepCovers`, `vacatedHolding_of_keptOnCore`); its save stage writes the frame it trapped
   with into the resident thread's TCB
   (`saveCapturedTrapFrame_saves_resident`,
   `saveCapturedSyscallFrame_saves_resident`); and its tail leaves the core
   holding no registers but its current thread's
   (`SystemState.holdsOnlyCurrentOn`, at every committing entry).
3. **The HAL obligation** (`RemoteSaveObligation`): what the Rust side must
   hold for (2) to apply — the record, the sample under the lock, the wait
   outside it, and the frame the target's entry is handed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-! ### The target's state at its entry -/

/-- Core `d` is vacated and holds `t`'s live registers, or holds nobody's: the
state a stalled target is in until its next entry. -/
def _root_.SeLe4n.Model.SystemState.vacatedHolding (st : SystemState) (d : CoreId) (t : SeLe4n.ThreadId) : Prop :=
  st.scheduler.currentOnCore d = none ∧
    (st.machine.residentOnCore d = some t ∨ st.machine.residentOnCore d = none)

/-- `S` holds on core `d` no current or resident thread that `P` did not hold
there: the cross-core frame of a step on another core, and of any run of them. -/
def keptOnCore (d : CoreId) (P S : SystemState) : Prop :=
  (∀ u, S.scheduler.currentOnCore d = some u → P.scheduler.currentOnCore d = some u) ∧
    (∀ u, S.machine.residentOnCore d = some u → P.machine.residentOnCore d = some u)

theorem keptOnCore_refl (d : CoreId) (P : SystemState) : keptOnCore d P P :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem keptOnCore_trans {d : CoreId} {P Q S : SystemState} (h₁ : keptOnCore d P Q)
    (h₂ : keptOnCore d Q S) : keptOnCore d P S :=
  ⟨fun u h => h₁.1 u (h₂.1 u h), fun u h => h₁.2 u (h₂.2 u h)⟩

/-- **A step on another core keeps the target's slots**: it makes no thread
current or resident there (`stepCovers`'s `currentKept` and `residentKept`). -/
theorem keptOnCore_of_stepCovers {e d : CoreId} {P S : SystemState} (hd : d ≠ e)
    (hC : stepCovers e P S) : keptOnCore d P S :=
  ⟨hC.currentKept d hd, hC.residentKept d hd⟩

/-- **Whatever other cores commit, the stalled target stays vacated and holds
the thread or nobody.** -/
theorem vacatedHolding_of_keptOnCore {d : CoreId} {P S : SystemState} {t : SeLe4n.ThreadId}
    (hK : keptOnCore d P S) (h : P.vacatedHolding d t) : S.vacatedHolding d t := by
  obtain ⟨hCur, hRes⟩ := h
  refine ⟨?_, ?_⟩
  · cases hS : S.scheduler.currentOnCore d with
    | none => rfl
    | some u => have := hK.1 u hS; rw [hCur] at this; cases this
  · cases hS : S.machine.residentOnCore d with
    | none => exact Or.inr rfl
    | some u =>
      have hP := hK.2 u hS
      rcases hRes with hR | hR <;> rw [hR] at hP
      · cases hP; exact Or.inl rfl
      · cases hP

/-! ### The target's save stage -/

/-- **The save stage of a vacated core's entry writes the frame into the
thread the core holds.** -/
theorem saveCapturedTrapFrame_saves_resident (st : SystemState) (d : CoreId)
    (ic : Architecture.InFlightContext) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hEl0 : Architecture.trapFromEl0 ic.snapshot = true)
    (hCur : st.scheduler.currentOnCore d = none) (hRes : st.machine.residentOnCore d = some t)
    (hTcb : st.getTcb? t = some tcb) (hInv : st.objects.invExt) :
    (Architecture.saveCapturedTrapFrame st d (some ic)).getTcb? t =
      some { tcb with registerContext := ic.snapshot } := by
  simp only [Architecture.saveCapturedTrapFrame]
  rw [Architecture.saveTrapFrameOnCore_of_idle st d _ hCur]
  exact Architecture.saveVacatedFrameOnCore_saves st d _ _ t tcb hEl0 hCur hRes hTcb hInv

/-- ...and a syscall entry's, rewound to the `SVC`, so the thread re-issues the
syscall the stall interrupted. -/
theorem saveCapturedSyscallFrame_saves_resident (st : SystemState) (d : CoreId)
    (ic : Architecture.InFlightContext) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hEl0 : Architecture.trapFromEl0 ic.snapshot = true)
    (hCur : st.scheduler.currentOnCore d = none) (hRes : st.machine.residentOnCore d = some t)
    (hTcb : st.getTcb? t = some tcb) (hInv : st.objects.invExt) :
    (Architecture.saveCapturedSyscallFrame st d (some ic)).getTcb? t =
      some { tcb with registerContext := Architecture.restartAtSvc ic.snapshot } := by
  simp only [Architecture.saveCapturedSyscallFrame]
  rw [Architecture.saveTrapFrameOnCore_of_idle st d _ hCur]
  exact Architecture.saveVacatedFrameOnCore_saves st d _ _ t tcb hEl0 hCur hRes hTcb hInv

/-- The per-core entries' raw-id form of the save. -/
theorem saveCapturedTrapFrameAt_saves_resident (st : SystemState) (coreId : UInt64) (d : CoreId)
    (hd : Concurrency.coreIdOfUInt64? coreId = some d)
    (ic : Architecture.InFlightContext) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hEl0 : Architecture.trapFromEl0 ic.snapshot = true)
    (hCur : st.scheduler.currentOnCore d = none) (hRes : st.machine.residentOnCore d = some t)
    (hTcb : st.getTcb? t = some tcb) (hInv : st.objects.invExt) :
    (Concurrency.saveCapturedTrapFrameAt st coreId (some ic)).getTcb? t =
      some { tcb with registerContext := ic.snapshot } := by
  simp only [Concurrency.saveCapturedTrapFrameAt, hd]
  exact saveCapturedTrapFrame_saves_resident st d ic t tcb hEl0 hCur hRes hTcb hInv

theorem saveCapturedSyscallFrameAt_saves_resident (st : SystemState) (coreId : UInt64)
    (d : CoreId) (hd : Concurrency.coreIdOfUInt64? coreId = some d)
    (ic : Architecture.InFlightContext) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hEl0 : Architecture.trapFromEl0 ic.snapshot = true)
    (hCur : st.scheduler.currentOnCore d = none) (hRes : st.machine.residentOnCore d = some t)
    (hTcb : st.getTcb? t = some tcb) (hInv : st.objects.invExt) :
    (Concurrency.saveCapturedSyscallFrameAt st coreId (some ic)).getTcb? t =
      some { tcb with registerContext := Architecture.restartAtSvc ic.snapshot } := by
  simp only [Concurrency.saveCapturedSyscallFrameAt, hd]
  exact saveCapturedSyscallFrame_saves_resident st d ic t tcb hEl0 hCur hRes hTcb hInv

/-! ### The target's tail: it holds no registers but its current thread's -/

/-- **Core `c` holds no thread's live registers but its current thread's**:
the state a core's entry leaves it in, so a stalled target's entry has released
the thread the commit took off it (its save stage wrote the frame first). -/
def _root_.SeLe4n.Model.SystemState.holdsOnlyCurrentOn (st : SystemState) (c : CoreId) : Prop :=
  ∀ t, st.machine.residentOnCore c = some t → st.scheduler.currentOnCore c = some t

/-- The property reads only the core's current slot and residency record. -/
theorem _root_.SeLe4n.Model.SystemState.holdsOnlyCurrentOn_of_frame {st st' : SystemState} {c : CoreId}
    (hS : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hR : st'.machine.residentCode = st.machine.residentCode)
    (h : st.holdsOnlyCurrentOn c) : st'.holdsOnlyCurrentOn c := by
  intro t ht
  rw [hS]; apply h
  unfold MachineState.residentOnCore at ht ⊢; rw [← hR]; exact ht

/-- **The residency settle leaves the core holding only its current thread**:
it records the current thread when the core resumes it at EL0, and nobody
otherwise. -/
theorem settleResidencyOnCore_holdsOnlyCurrentOn (st : SystemState) (c : CoreId) :
    (PriorityInheritance.settleResidencyOnCore st c).holdsOnlyCurrentOn c := by
  intro t h
  rw [PriorityInheritance.settleResidencyOnCore_resident] at h
  rw [PriorityInheritance.settleResidencyOnCore_currentOnCore]
  split at h
  · exact h
  · cases h

/-- The activation writes the core's bank and a TCB, never a slot or a record. -/
theorem activateThreadOnCore_holdsOnlyCurrentOn (st : SystemState) (c d : CoreId)
    (h : st.holdsOnlyCurrentOn d) : (activateThreadOnCore st c).holdsOnlyCurrentOn d :=
  SystemState.holdsOnlyCurrentOn_of_frame (by rw [activateThreadOnCore_scheduler])
    (by rw [activateThreadOnCore_machine_eq_regs]) h

/-- **An entry's tail on the core its raw id names**: settle, then activation. -/
theorem entryTailAt_holdsOnlyCurrentOn (M : SystemState) (coreId : UInt64) (c : CoreId)
    (hc : Concurrency.coreIdOfUInt64? coreId = some c) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt M coreId) coreId).holdsOnlyCurrentOn c := by
  simp only [activateThreadAt, PriorityInheritance.settleResidencyAt, hc]
  exact activateThreadOnCore_holdsOnlyCurrentOn _ c c (settleResidencyOnCore_holdsOnlyCurrentOn M c)

/-- ...and with the entry's two ledger clears after it, which write neither a
slot nor a record. -/
theorem entryTailAt_cleared_holdsOnlyCurrentOn (M : SystemState) (coreId : UInt64) (c : CoreId)
    (hc : Concurrency.coreIdOfUInt64? coreId = some c) :
    (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
      (activateThreadAt (PriorityInheritance.settleResidencyAt M coreId) coreId))).holdsOnlyCurrentOn c :=
  SystemState.holdsOnlyCurrentOn_of_frame rfl rfl (entryTailAt_holdsOnlyCurrentOn M coreId c hc)

/-- **The timer entry leaves its core holding only its current thread.** -/
theorem perCoreTimerTickEntryState_holdsOnlyCurrentOn (coreId : UInt64) (c : CoreId)
    (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (st : SystemState) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))).holdsOnlyCurrentOn c :=
  entryTailAt_cleared_holdsOnlyCurrentOn _ coreId c hc

/-- **The reschedule entry leaves its core holding only its current thread** —
the entry a stalled target's exit gate runs when it refuses the return to EL0,
and the secondary core's first entry. -/
theorem perCoreRescheduleEntryState_holdsOnlyCurrentOn (coreId : UInt64) (c : CoreId)
    (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (st : SystemState) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))).holdsOnlyCurrentOn c :=
  entryTailAt_cleared_holdsOnlyCurrentOn _ coreId c hc

/-- **The fault entry leaves its core holding only its current thread.** -/
theorem faultEntryState_holdsOnlyCurrentOn (lctx : LabelingContext) (coreId : UInt64)
    (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx
        (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).holdsOnlyCurrentOn c :=
  entryTailAt_cleared_holdsOnlyCurrentOn _ coreId c hc

/-- **The unknown-syscall entry leaves its core holding only its current
thread.** -/
theorem unknownSyscallEntryState_holdsOnlyCurrentOn (lctx : LabelingContext) (coreId : UInt64)
    (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).holdsOnlyCurrentOn c :=
  entryTailAt_cleared_holdsOnlyCurrentOn _ coreId c hc

/-- **The FP/SIMD entry leaves its core holding only its current thread.** -/
theorem fpAccessEntryState_holdsOnlyCurrentOn (coreId : UInt64) (c : CoreId)
    (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext) (st : SystemState) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId)
        coreId).holdsOnlyCurrentOn c :=
  entryTailAt_holdsOnlyCurrentOn _ coreId c hc

/-- Clearing the entry's ledgers touches neither the current slots nor the
residency record. -/
theorem holdsOnlyCurrentOn_clearLedgers {X : SystemState} {c : CoreId}
    (h : X.holdsOnlyCurrentOn c) :
    (Architecture.clearPhysicalWrites
      (Architecture.clearIcacheMaintenance X)).holdsOnlyCurrentOn c :=
  SystemState.holdsOnlyCurrentOn_of_frame rfl rfl h

/-- **The syscall entry leaves its core holding only its current thread.** -/
theorem syscallDispatchEntryState_holdsOnlyCurrentOn (ctx : LabelingContext)
    (e : CoreId) (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e syscallId trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2).holdsOnlyCurrentOn e := by
  refine SystemState.holdsOnlyCurrentOn_of_frame
    (by unfold Architecture.IpcBufferRead.clearUserWords
        rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
    (syncUserWords_residentCode _ _ _) ?_
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
    trapped.pstate trapped.sp trapped.x30
    (Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame) bytes n)
  show (syscallDispatchCrossCoreStep ctx e syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
    trapped.pstate trapped.sp trapped.x30
    (Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
      bytes n)).2.holdsOnlyCurrentOn e
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  dsimp only
  exact holdsOnlyCurrentOn_clearLedgers
    (activateThreadOnCore_holdsOnlyCurrentOn _ e e (settleResidencyOnCore_holdsOnlyCurrentOn _ e))

/-! ### The HAL obligation -/

/-- **What the HAL's stall must hold** (`rust/sele4n-hal/src/remote_stall.rs`)
for an initiator's commit `pre → post` on core `e`, stated over the run that
follows it.  `decided` is the HAL record (`PER_CPU_CURRENT_THREAD`) at the
commit, and for each stalled core `d` (`Concurrency.stallsOn decided e post d`) the run
names the state `entry` the target's first locked entry after the commit ran
from (a parameter, not a field: the obligation is about a state the run
reached, not a function that makes one), and the frame that entry saved:

* `record`: the record names what each core runs — every committing entry
  records what it left its own core running (`recordCommittedCurrentThreadHw`),
  and nothing else writes a core's slot of it;
* `between`: the commits other cores made between the initiator's and the
  target's entry are steps on cores other than `d` (the kernel-entry lock
  serialises them; `stepCovers` is each one's frame), so they kept `d`'s slots
  (`keptOnCore`);
* `frame`: the target's entry is handed the frame of the thread it ran, from
  EL0 — an exception from EL0, or the exit gate's refused return, which hands
  the frame it was about to resume;
* the wait, which is why `entry` precedes the initiator's return: the
  initiator returns to EL0 only after that entry has committed —
  the save epoch the target advances inside the lock
  (`note_locked_entry_in`), sampled under the initiator's lock
  (`record_pending_save_in`) and waited on outside it
  (`await_remote_saves_in`).

`RemoteSaveObligation.saved` is what the stall then guarantees. -/
structure RemoteSaveObligation (e d : CoreId) (pre post entry : SystemState) (t : SeLe4n.ThreadId) where
  /-- The target is another core. -/
  ne : d ≠ e
  /-- The HAL record at the commit. -/
  decided : Vector Nat Concurrency.numCores
  /-- The record names the thread the target ran. -/
  record : decided.get d = SeLe4n.ThreadId.optCode (some t)
  /-- The target ran `t` at EL0: its last settle recorded `t` resident. -/
  ran : pre.machine.residentOnCore d = some t
  /-- The commit took `t` off the target. -/
  vacated : post.scheduler.currentOnCore d = none
  /-- The commit made no thread resident on the target. -/
  kept : keptOnCore d pre post
  /-- The commits between kept the target's slots. -/
  between : keptOnCore d post entry
  /-- The frame the target's entry saved, taken from EL0. -/
  frame : Architecture.InFlightContext
  fromEl0 : Architecture.trapFromEl0 frame.snapshot = true
  /-- The store's table invariant at the target's entry. -/
  invExt : entry.objects.invExt

/-- **The target is stalled**: the HAL's check finds it changed. -/
theorem RemoteSaveObligation.stalled {e d : CoreId} {pre post entry : SystemState}
    {t : SeLe4n.ThreadId} (O : RemoteSaveObligation e d pre post entry t) :
    Concurrency.stallsOn O.decided e post d = true :=
  Concurrency.stallsOn_of_taken O.decided e d post t O.ne O.record (by rw [O.vacated]; simp)

/-- **What the stall guarantees**: by the time the initiator returns, the
target's entry has written the frame `t` trapped with into `t`'s TCB — or `t`'s
record was released first, by the final delete of `t` — and the target holds
no thread's registers but its own current thread's (every entry's tail,
`*EntryState_holdsOnlyCurrentOn`). -/
theorem RemoteSaveObligation.saved {e d : CoreId} {pre post entry : SystemState}
    {t : SeLe4n.ThreadId} (O : RemoteSaveObligation e d pre post entry t) :
    (∀ tcb, entry.getTcb? t = some tcb →
        entry.machine.residentOnCore d = some t →
        (Architecture.saveCapturedTrapFrame entry d (some O.frame)).getTcb? t =
            some { tcb with registerContext := O.frame.snapshot } ∧
          (Architecture.saveCapturedSyscallFrame entry d (some O.frame)).getTcb? t =
            some { tcb with registerContext := Architecture.restartAtSvc O.frame.snapshot }) ∧
      entry.vacatedHolding d t := by
  have hP : post.vacatedHolding d t := by
    refine ⟨O.vacated, ?_⟩
    cases h : post.machine.residentOnCore d with
    | none => exact Or.inr rfl
    | some u =>
      have := O.kept.2 u h
      rw [O.ran] at this
      cases this
      exact Or.inl rfl
  have hV := vacatedHolding_of_keptOnCore O.between hP
  refine ⟨fun tcb hT hR => ⟨?_, ?_⟩, hV⟩
  · exact saveCapturedTrapFrame_saves_resident _ d _ t tcb O.fromEl0 hV.1 hR hT O.invExt
  · exact saveCapturedSyscallFrame_saves_resident _ d _ t tcb O.fromEl0 hV.1 hR hT O.invExt

end SeLe4n.Kernel
