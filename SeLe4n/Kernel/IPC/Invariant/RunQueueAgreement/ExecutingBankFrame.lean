/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.OffCoreContextMatches

/-!
# The executing core's bank across a syscall

A syscall's entry saves the trapped frame into its caller's context and into the
executing core's bank, so the two agree when the dispatch starts
(`syscallEntrySaved_contextMatchesCurrentOnCore`).  The dispatch's arms then
write the caller's return window (`x0`–`x5`) into its context alone: a delivered
message, a queried word, a consumed time.  The bank catches up only at the
commit, where `Architecture.stageCallerReturnFor` writes the outcome's frame
into both.

So between the entry and the commit the bank and the caller's context agree
everywhere *but* the return window, and every other thread a scheduling point
makes current agrees with the bank outright.  `bankAgree` states that;
`bankFrame` is a step that keeps it without a scheduling point (the bank, the
core's current slot, and each current thread's context off the caller's window
kept); a scheduling point keeps it by establishing the match or by leaving the
core as it found it.  The commit's staging then turns it into the match.

The frames come from the census of another core: a step whose saved-register
census and coverage hold at a core `e'` other than `e` keeps `e`'s bank and
current slot and writes no thread current on `e` (`bankFrame.of_offCore`).
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- A register file with its return window (`x0`–`x5`) cleared. -/
def _root_.SeLe4n.RegisterFile.offFrame (r : SeLe4n.RegisterFile) : SeLe4n.RegisterFile :=
  { r with x0 := 0, x1 := 0, x2 := 0, x3 := 0, x4 := 0, x5 := 0 }

@[simp] theorem _root_.SeLe4n.RegisterFile.offFrame_stageReturnFrame (r : SeLe4n.RegisterFile)
    (f : Architecture.SyscallReturnFrame) : (r.stageReturnFrame f).offFrame = r.offFrame := rfl

@[simp] theorem _root_.SeLe4n.RegisterFile.offFrame_withConsumed (r : SeLe4n.RegisterFile)
    (w : UInt64) : (r.withConsumed w).offFrame = r.offFrame := rfl

@[simp] theorem _root_.SeLe4n.RegisterFile.offFrame_stageReturnWords (r : SeLe4n.RegisterFile)
    (w0 w1 w2 w3 w4 w5 : UInt64) :
    (Architecture.stageReturnWords r w0 w1 w2 w3 w4 w5).offFrame = r.offFrame := rfl

/-- **A staged frame erases the difference in the return window**: two files
that agree off the window agree once a frame is staged into both. -/
theorem _root_.SeLe4n.RegisterFile.stageReturnFrame_of_offFrame {a b : SeLe4n.RegisterFile}
    (h : a.offFrame = b.offFrame) (f : Architecture.SyscallReturnFrame) :
    a.stageReturnFrame f = b.stageReturnFrame f := by
  show (a.offFrame).stageReturnFrame f = (b.offFrame).stageReturnFrame f
  rw [h]

/-- The part of thread `t`'s context the bank must match: all of it, but for the
caller `c0`, whose return window the dispatch stages ahead of the bank. -/
def maskRegs (c0 t : SeLe4n.ThreadId) (r : SeLe4n.RegisterFile) : SeLe4n.RegisterFile :=
  if t = c0 then r.offFrame else r

/-- WS-ZA ZA6.28: **core `e`'s bank agrees with its current thread's saved
context**, off the caller `c0`'s return window. -/
def bankAgree (e : CoreId) (c0 : SeLe4n.ThreadId) (s : SystemState) : Prop :=
  ∀ t, s.scheduler.currentOnCore e = some t → ∀ r, s.savedRegs t = some r →
    maskRegs c0 t (s.machine.regsOnCore e) = maskRegs c0 t r

/-- The match is the agreement with nothing masked. -/
theorem bankAgree_of_match {e : CoreId} {c0 : SeLe4n.ThreadId} {s : SystemState}
    (h : contextMatchesCurrentOnCore s e) : bankAgree e c0 s := by
  intro t ht r hr
  unfold contextMatchesCurrentOnCore at h
  rw [ht] at h
  unfold SystemState.savedRegs at hr
  cases hT : s.getTcb? t with
  | none => rw [hT] at hr; cases hr
  | some tcb =>
    rw [hT] at hr
    simp only [hT] at h
    cases hr
    rw [(RegisterFile.beq_iff_eq' _ _).mp h]

/-- A core with no current thread agrees vacuously. -/
theorem bankAgree_of_none {e : CoreId} {c0 : SeLe4n.ThreadId} {s : SystemState}
    (h : s.scheduler.currentOnCore e = none) : bankAgree e c0 s := fun t ht => by
  rw [h] at ht; cases ht

/-- **Away from the caller the agreement is the match**: a current thread other
than `c0` has nothing masked. -/
theorem contextMatchesCurrentOnCore_of_bankAgree {e : CoreId} {c0 : SeLe4n.ThreadId}
    {s : SystemState} (h : bankAgree e c0 s) (hNe : s.scheduler.currentOnCore e ≠ some c0) :
    contextMatchesCurrentOnCore s e := by
  unfold contextMatchesCurrentOnCore
  split
  · rename_i t ht
    split
    · rename_i tcb hT
      have hA := h t ht tcb.registerContext (by unfold SystemState.savedRegs; rw [hT]; rfl)
      have hNe' : t ≠ c0 := fun e => hNe (e ▸ ht)
      simp only [maskRegs, hNe', if_false] at hA
      rw [hA]; exact RegisterFile.beq_self _
    · trivial
  · trivial

/-- WS-ZA ZA6.28: **a step that keeps the executing core's agreement without a
scheduling point**: core `e`'s bank and current slot kept (a thread current
after was current before), and each thread current after keeps its context off
the caller's return window. -/
structure bankFrame (e : CoreId) (c0 : SeLe4n.ThreadId) (pre post : SystemState) : Prop where
  bank : post.machine.regsOnCore e = pre.machine.regsOnCore e
  current : currentKeptOnCore e pre post
  regs : ∀ t, post.scheduler.currentOnCore e = some t →
    (post.savedRegs t).map (maskRegs c0 t) = (pre.savedRegs t).map (maskRegs c0 t)

namespace bankFrame

variable {e : CoreId} {c0 : SeLe4n.ThreadId}

theorem refl (st : SystemState) : bankFrame e c0 st st :=
  ⟨rfl, .refl st, fun _ _ => rfl⟩

theorem trans {a b c : SystemState} (h₁ : bankFrame e c0 a b) (h₂ : bankFrame e c0 b c) :
    bankFrame e c0 a c :=
  ⟨h₂.bank.trans h₁.bank, h₁.current.trans h₂.current,
    fun t ht => (h₂.regs t ht).trans (h₁.regs t (h₂.current t ht))⟩

theorem of_eq {pre post : SystemState} (h : post = pre) : bankFrame e c0 pre post := by
  subst h; exact refl _

/-- **The agreement is carried across the step.** -/
theorem bankAgree {pre post : SystemState} (f : bankFrame e c0 pre post)
    (h : SeLe4n.Kernel.bankAgree e c0 pre) : SeLe4n.Kernel.bankAgree e c0 post := by
  intro t ht r hr
  have hR := f.regs t ht
  rw [hr] at hR
  cases hP : pre.savedRegs t with
  | none => rw [hP] at hR; cases hR
  | some r' =>
    rw [hP] at hR
    simp only [Option.map_some, Option.some.injEq] at hR
    rw [f.bank, hR]
    exact h t (f.current t ht) r' hP

/-- WS-ZA ZA6.28: **a step another core's census covers keeps the agreement**:
coverage at a core `e'` other than `e` keeps `e`'s bank and current slot, and a
census at `e'` keeps the saved context of every thread current on `e`. -/
theorem of_offCore {e' : CoreId} {pre post : SystemState} (hne : e ≠ e')
    (hC : stepCovers e' pre post) (hS : savedRegsKeptOffCore e' pre post) :
    bankFrame e c0 pre post :=
  ⟨hC.banksKept e hne, fun t ht => hC.currentKept e hne t ht,
    fun t ht => by rw [hS e hne t (.inl ht)]⟩

/-- The census at `e'` read off the threads a step writes. -/
theorem of_writtenFree {e' : CoreId} {pre post : SystemState} (hne : e ≠ e')
    (hC : stepCovers e' pre post) (hW : savedRegsWrittenFree e' pre pre post) :
    bankFrame e c0 pre post :=
  of_offCore hne hC (hW.census hC.currentKept hC.residentKept)

/-- A covered step that writes no saved register. -/
theorem of_kept {e' : CoreId} {pre post : SystemState} (hne : e ≠ e')
    (hC : stepCovers e' pre post) (hK : savedRegsKeptExcept (fun _ => False) pre post) :
    bankFrame e c0 pre post :=
  of_writtenFree hne hC (.of_kept hK fun _ h => h.elim)

/-- A covered step that writes no saved register. -/
theorem of_unwritten {e' : CoreId} {pre post : SystemState} (hne : e ≠ e')
    (hC : stepCovers e' pre post) (hU : savedRegsUnwritten pre post) :
    bankFrame e c0 pre post :=
  of_writtenFree hne hC hU.writtenFree

end bankFrame

/-- WS-ZA ZA6.28: **a step that writes every thread's context off the caller's
return window as it found it**: the caller's window may change, nothing else. -/
def regsMaskKept (c0 : SeLe4n.ThreadId) (pre post : SystemState) : Prop :=
  ∀ t, (post.savedRegs t).map (maskRegs c0 t) = (pre.savedRegs t).map (maskRegs c0 t)

namespace regsMaskKept

variable {c0 : SeLe4n.ThreadId}

theorem refl (st : SystemState) : regsMaskKept c0 st st := fun _ => rfl

theorem trans {a b c : SystemState} (h₁ : regsMaskKept c0 a b) (h₂ : regsMaskKept c0 b c) :
    regsMaskKept c0 a c := fun t => (h₂ t).trans (h₁ t)

/-- A step that writes no saved register. -/
theorem of_kept {pre post : SystemState} (k : savedRegsKeptExcept (fun _ => False) pre post) :
    regsMaskKept c0 pre post := fun t => by rw [k t id]

/-- A write of the caller's return window. -/
theorem updateTcb_caller {s : SystemState} (f : TCB → TCB) (hInv : s.objects.invExt)
    (hf : ∀ x, (f x).registerContext.offFrame = x.registerContext.offFrame) :
    regsMaskKept c0 s (s.updateTcb c0 f) := fun t => by
  by_cases hT : t = c0
  · subst hT
    unfold SystemState.savedRegs
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv]
    cases s.getTcb? t with
    | none => rfl
    | some x => simp [maskRegs, hf]
  · rw [savedRegs_updateTcb_ne hInv hT]

end regsMaskKept

namespace bankFrame

variable {e : CoreId} {c0 : SeLe4n.ThreadId}

/-- A covered step that writes the caller's return window alone. -/
theorem of_maskKept {e' : CoreId} {pre post : SystemState} (hne : e ≠ e')
    (hC : stepCovers e' pre post) (h : regsMaskKept c0 pre post) : bankFrame e c0 pre post :=
  ⟨hC.banksKept e hne, fun t ht => hC.currentKept e hne t ht, fun t _ => h t⟩

/-- A step that writes no object, no scheduler state and not core `e`'s bank. -/
theorem of_frame {pre post : SystemState} (hO : post.objects = pre.objects)
    (hS : post.scheduler = pre.scheduler)
    (hM : post.machine.regsOnCore e = pre.machine.regsOnCore e) : bankFrame e c0 pre post :=
  ⟨hM, .of_eq (by rw [hS]), fun t _ => by
    unfold SystemState.savedRegs SystemState.getTcb?; rw [hO]⟩

/-- The physical-write ledger is no object, no scheduler state and no bank. -/
theorem recordPhysicalWrites (s : SystemState) (ws : List Architecture.PhysicalWrite) :
    bankFrame e c0 s (Architecture.recordPhysicalWrites s ws) :=
  of_frame (Architecture.recordPhysicalWrites_objects _ _)
    (Architecture.recordPhysicalWrites_scheduler _ _)
    (by rw [Architecture.recordPhysicalWrites_machine])

/-- **A write of the caller's return window keeps the agreement**: it changes the
caller's context in the window alone and every other thread's not at all. -/
theorem updateTcb_caller {s : SystemState} (f : TCB → TCB) (hInv : s.objects.invExt)
    (hf : ∀ x, (f x).registerContext.offFrame = x.registerContext.offFrame) :
    bankFrame e c0 s (s.updateTcb c0 f) :=
  ⟨by rw [SystemState.updateTcb_machine], .of_eq (by rw [SystemState.updateTcb_scheduler]),
    fun t _ => regsMaskKept.updateTcb_caller f hInv hf t⟩

/-- A return frame staged into the caller. -/
theorem writeReturnFrameToTcb_caller {s : SystemState} (f : Architecture.SyscallReturnFrame)
    (hInv : s.objects.invExt) : bankFrame e c0 s (Architecture.writeReturnFrameToTcb s c0 f) :=
  updateTcb_caller _ hInv fun _ => rfl

/-- **A delivered message staged into the caller keeps the agreement**: its frame
lands in the caller's return window, and the overflow words in memory. -/
theorem stageDeliveredMessage_caller {s : SystemState} (n : Nat) (hInv : s.objects.invExt) :
    bankFrame e c0 s (Architecture.stageDeliveredMessage s c0 n) := by
  unfold Architecture.stageDeliveredMessage
  split
  · split
    · split
      · unfold Architecture.writeDeliveredFrameToTcb
        refine trans ?_ (recordPhysicalWrites _ _)
        exact updateTcb_caller _ hInv fun _ => rfl
      · exact refl _
    · exact refl _
  · exact refl _

/-- The caller's delivered message, when the arm names the caller. -/
theorem stageWokenDelivery_caller {s : SystemState} (n : Nat) (hInv : s.objects.invExt) :
    bankFrame e c0 s (Architecture.stageWokenDelivery s (some c0) n) :=
  stageDeliveredMessage_caller n hInv

end bankFrame

/-! ### The scheduling points

A scheduling point either makes a thread other than the core's current one
current, restoring that thread's context into the bank (the match), or leaves
the core's bank, slot and current thread as they were. -/

/-- **The switch keeps the agreement**: a self-switch leaves the bank, the slot
and the thread's context as they were; any other switch restores the incoming
thread's context into the bank. -/
theorem bankAgree_switchToThreadOnCore {e : CoreId} {c0 tid : SeLe4n.ThreadId}
    {st st' : SystemState} (hInv : st.objects.invExt) (hA : bankAgree e c0 st)
    (h : switchToThreadOnCore st e tid = .ok st') : bankAgree e c0 st' := by
  have hPre : ∃ tidTcb, st.getTcb? tid = some tidTcb := by
    cases hTcb : st.getTcb? tid with
    | none => simp [switchToThreadOnCore, hTcb] at h
    | some t => exact ⟨t, rfl⟩
  obtain ⟨tidTcb, hTcb⟩ := hPre
  obtain ⟨t', hgt, hE⟩ := switchToThreadOnCore_getTcb?_incoming st e tid st' tidTcb hTcb hInv h
  have hCur := switchToThreadOnCore_sets_current st e tid st' h
  have hCtx : t'.registerContext = tidTcb.registerContext :=
    TCB.proj_eq_of_withoutRunLinks_eq TCB.registerContext hE
  intro t ht r hr
  rw [hCur] at ht; cases ht
  unfold SystemState.savedRegs at hr
  rw [hgt] at hr; cases hr
  by_cases hself : st.scheduler.currentOnCore e = some tid
  · rw [switchToThreadOnCore_self_regsOnCore st e tid st' hself h, hCtx]
    exact hA tid hself _ (by unfold SystemState.savedRegs; rw [hTcb]; rfl)
  · rw [switchToThreadOnCore_machine_regsOnCore_self st e tid st' tidTcb hTcb hInv hself h, hCtx]

/-- **The reschedule handler keeps the agreement**: a switch keeps it, a drop
leaves no current thread, and every other path is the identity. -/
theorem bankAgree_handleRescheduleSgiOnCore {e : CoreId} {c0 : SeLe4n.ThreadId}
    {st st' : SystemState} (hInv : st.objects.invExt) (hA : bankAgree e c0 st)
    (h : handleRescheduleSgiOnCore st e = .ok st') : bankAgree e c0 st' := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rw [Except.ok.injEq] at h; subst h
      exact bankAgree_of_match (dropCurrentOnCore_contextMatchesCurrentOnCore st e)
    · rw [Except.ok.injEq] at h; subst h; exact hA
  · split at h
    · split at h
      · rename_i sSw hSw
        rw [Except.ok.injEq] at h; subst h
        have hS := bankAgree_switchToThreadOnCore hInv hA hSw
        exact hS
      · split at h
        · rw [Except.ok.injEq] at h; subst h
          exact bankAgree_of_match (dropCurrentOnCore_contextMatchesCurrentOnCore st e)
        · rw [Except.ok.injEq] at h; subst h; exact hA
    · rw [Except.ok.injEq] at h; subst h; exact hA

/-- A scheduling point an arm may end with: none, or the reschedule handler. -/
theorem bankAgree_schedPoint {e : CoreId} {c0 : SeLe4n.ThreadId} {s s' : SystemState}
    (hInv : s.objects.invExt) (hA : bankAgree e c0 s)
    (h : s' = s ∨ handleRescheduleSgiOnCore s e = .ok s') : bankAgree e c0 s' := by
  rcases h with rfl | h
  · exact hA
  · exact bankAgree_handleRescheduleSgiOnCore hInv hA h

/-! ### The commit's staging -/

/-- A lookup reads the object store alone. -/
theorem getTcb?_of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects)
    (tid : SeLe4n.ThreadId) : st'.getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?; rw [h]

/-- **A bank write's match**: replacing the machine, the match reads the new
bank against the current thread's saved context. -/
theorem contextMatchesCurrentOnCore_setMachine (s : SystemState) (m : MachineState) (e : CoreId)
    (h : ∀ t tcb, s.scheduler.currentOnCore e = some t → s.getTcb? t = some tcb →
      m.regsOnCore e = tcb.registerContext) :
    contextMatchesCurrentOnCore { s with machine := m } e := by
  show (match s.scheduler.currentOnCore e with
    | some tid => match s.getTcb? tid with
      | some tcb => (m.regsOnCore e == tcb.registerContext) = true
      | none => True
    | none => True)
  split
  · rename_i t ht
    split
    · rename_i tcb hT
      rw [h t tcb ht hT]; exact RegisterFile.beq_self _
    · trivial
  · trivial

/-- The match read off its parts. -/
theorem contextMatchesCurrentOnCore_of_parts {s : SystemState} {e : CoreId}
    {t : SeLe4n.ThreadId} {tcb : TCB} (hC : s.scheduler.currentOnCore e = some t)
    (hT : s.getTcb? t = some tcb) (hB : s.machine.regsOnCore e = tcb.registerContext) :
    contextMatchesCurrentOnCore s e := by
  unfold contextMatchesCurrentOnCore
  simp only [hC, hT, hB]
  exact RegisterFile.beq_self _

/-- **The commit's staging of a returning caller makes the agreement the
match**: when the caller is still current its frame is staged into its context
and the bank alike, which agreed off the frame; otherwise the core's current
thread is another, which agreed outright, and the staging writes the caller
alone. -/
theorem contextMatchesCurrentOnCore_stageReturns {e : CoreId} {c0 : SeLe4n.ThreadId}
    {post : SystemState} (f : Architecture.SyscallReturnFrame) (hInv : post.objects.invExt)
    (hA : bankAgree e c0 post) :
    contextMatchesCurrentOnCore
      (Architecture.stageCallerReturnFor (some c0) post e (.returns f)) e := by
  unfold Architecture.stageCallerReturnFor
  dsimp only
  split
  · rename_i hCur
    refine contextMatchesCurrentOnCore_setMachine _ _ e fun t tcb' ht hT' => ?_
    rw [Architecture.writeReturnFrameToTcb_scheduler_eq, hCur] at ht
    cases ht
    unfold Architecture.writeReturnFrameToTcb at hT'
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv] at hT'
    cases hT : post.getTcb? c0 with
    | none => rw [hT] at hT'; cases hT'
    | some tcb =>
      rw [hT] at hT'
      cases hT'
      have hE := hA c0 hCur tcb.registerContext (by unfold SystemState.savedRegs; rw [hT]; rfl)
      simp only [maskRegs, if_true] at hE
      simp only [Architecture.stageFrameRegs, Architecture.writeReturnFrameToTcb_machine_eq,
        MachineState.regsOnCore_setRegsOnCore_self]
      exact SeLe4n.RegisterFile.stageReturnFrame_of_offFrame hE f
  · rename_i hCur
    have hM := contextMatchesCurrentOnCore_of_bankAgree hA hCur
    unfold contextMatchesCurrentOnCore at hM ⊢
    simp only [Architecture.writeReturnFrameToTcb_scheduler_eq,
      Architecture.writeReturnFrameToTcb_machine_eq]
    split
    · rename_i t ht
      rw [ht] at hM
      have hNe : t ≠ c0 := fun e => hCur (e ▸ ht)
      unfold Architecture.writeReturnFrameToTcb
      rw [SystemState.updateTcb_getTcb?_ne _ _ _ hInv _
        (fun h => hNe (SeLe4n.ThreadId.toObjId_injective _ _ h).symm)]
      exact hM
    · trivial

/-- **Every outcome's staging keeps a match**: a returning frame is staged into
both holders or into a thread not current, and a blocked or faulted outcome
stages nothing. -/
theorem contextMatchesCurrentOnCore_stageCallerReturnFor {e : CoreId} {post : SystemState}
    (caller? : Option SeLe4n.ThreadId) (o : Architecture.SyscallOutcome)
    (hInv : post.objects.invExt) (h : contextMatchesCurrentOnCore post e) :
    contextMatchesCurrentOnCore (Architecture.stageCallerReturnFor caller? post e o) e := by
  cases caller? with
  | none => cases o <;> exact h
  | some c0 =>
    cases o with
    | returns f =>
      exact contextMatchesCurrentOnCore_stageReturns f hInv (bankAgree_of_match (c0 := c0) h)
    | blocks => exact h
    | faulted => exact h

/-- **The commit's staging turns the agreement into the match**, when an
outcome that stages nothing leaves the caller current no longer. -/
theorem contextMatchesCurrentOnCore_stageCallerReturnFor_of_bankAgree {e : CoreId}
    {c0 : SeLe4n.ThreadId} {post : SystemState} (o : Architecture.SyscallOutcome)
    (hInv : post.objects.invExt) (hA : bankAgree e c0 post)
    (hNR : (∀ f, o ≠ .returns f) → post.scheduler.currentOnCore e ≠ some c0) :
    contextMatchesCurrentOnCore (Architecture.stageCallerReturnFor (some c0) post e o) e := by
  cases o with
  | returns f => exact contextMatchesCurrentOnCore_stageReturns f hInv hA
  | blocks =>
    exact contextMatchesCurrentOnCore_of_bankAgree hA (hNR fun _ h => by cases h)
  | faulted =>
    exact contextMatchesCurrentOnCore_of_bankAgree hA (hNR fun _ h => by cases h)

/-- WS-ZA ZA6.28: **a scheduling arm keeps the agreement**: its prefix writes no
thread current on the core (each thread it writes was free of every core at
`base`, where the core's current thread already was), the core's bank or its
slot, and its scheduling point keeps the agreement. -/
theorem SchedPointPrefix.bankAgree {e : CoreId} {c0 : SeLe4n.ThreadId}
    {base st s st' : SystemState} (P : SchedPointPrefix e base st s st')
    (hBase : currentKeptOnCore e base st) (hA : SeLe4n.Kernel.bankAgree e c0 st) :
    SeLe4n.Kernel.bankAgree e c0 st' := by
  have F : bankFrame e c0 st s := ⟨P.bank, P.current, fun t ht => by
    rcases P.writes (otherCore e) t with k | hF
    · rw [k]
    · exact absurd (hBase t (P.current t ht)) ((hF e (ne_otherCore e)).1)⟩
  exact bankAgree_schedPoint P.inv (F.bankAgree hA) P.point

end SeLe4n.Kernel
