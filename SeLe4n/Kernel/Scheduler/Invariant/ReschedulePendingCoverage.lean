-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.ReschedulePending
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore

/-!
# The reschedule flags cover the commit diff

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md`, PR B.  A step `pre → post`
on executing core `e` **covers** a remote core `c` when it either raised (or
kept) `c`'s reschedule flag, or left `c`'s scheduling decision unstaled:
nothing joined `c`'s run queue (read off the threads' run-queue links, the
queue the chooser walks: WS-ZA ZA4.5), no queued thread's effective key moved,
`c`'s current slot is unchanged and its occupant's claim to the CPU did not
weaken (`coreDecisionUnstaled`).  The flags are allowed to over-approximate —
a raise that stales nothing costs one scheduling point that finds nothing to
do — so the relation is coverage, not equality.

The relation composes (`reschedulePendingCovers_trans`): a sequence of steps
each covering every remote core covers it end to end, provided no step lowers a
remote flag (`reschedulePendingMonotone`).  And it is what the commit needs
(`computeCrossCoreSgis_core_flagged_of_covers`): every core the whole-index
diff `computeCrossCoreSgis` names has its flag up in the post-state, so the
flag-derived list `rescheduleSgisFromFlags` names it unless it was already
pending at the step's start.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind allCores numCores)
open SeLe4n.Kernel.PriorityInheritance (crossCoreSgiBody currentSlotChangeSgis
  computeCrossCoreSgis)

/-- A thread's effective scheduling key as the diff compares it: the effective
priority, the effective deadline's value and the domain (`effectiveSchedParams`),
or `none` when no TCB is stored under the id. -/
def schedKeyView (st : SystemState) (t : SeLe4n.ThreadId) :
    Option (SeLe4n.Priority × Nat × SeLe4n.DomainId) :=
  (st.getTcb? t).map fun tcb =>
    ((effectiveSchedParams st tcb).1, (effectiveSchedParams st tcb).2.1.val,
      (effectiveSchedParams st tcb).2.2)

/-- The thread's claim to a CPU it holds did not weaken from `pre` to `post`:
its effective priority did not drop, its effective deadline did not move later
and its domain did not move (the selector admits only threads of the core's
active domain).  A thread with no TCB in `post` claims nothing. -/
def schedKeyNotWeakened (pre post : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∀ kq, schedKeyView post t = some kq →
    ∃ kp, schedKeyView pre t = some kp ∧ kp.1.val ≤ kq.1.val ∧ kq.2.1 ≤ kp.2.1 ∧
      kq.2.2 = kp.2.2

/-- Whether the chooser may pick a thread at all on budget grounds
(`hasSufficientBudget`: unbound, or bound to a context with budget left), or
`none` when no TCB is stored under the id.  The chooser reads this beside the
key (`chooseBestRunnableEffective`), so the coverage reads it too. -/
def budgetEligibleView (st : SystemState) (t : SeLe4n.ThreadId) : Option Bool :=
  (st.getTcb? t).map (hasSufficientBudget st)

/-- The thread did not become budget-eligible from `pre` to `post`.  A thread
that loses eligibility only leaves the set the chooser walks, which stales
nothing; one that gains it may now outrank the current thread. -/
def candidacyNotGained (pre post : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  budgetEligibleView post t = some true → budgetEligibleView pre t = some true

/-- Core `c`'s scheduling decision is not staled by `pre → post`: every thread
queued on `c` afterwards was queued there before with the same key and did not
become budget-eligible, the current slot is unchanged, and its occupant's claim
did not weaken.  (Removing a queued thread, a queued thread losing its budget,
or strengthening the current one, stales nothing.)  These are everything the
chooser and the reschedule gate read (`chooseBestRunnableEffective_eq_of_views`,
`handleRescheduleOnCoreDecision_eq_of_views`). -/
def coreDecisionUnstaled (pre post : SystemState) (c : CoreId) : Prop :=
  (∀ t, post.queuedOn c t = true →
      pre.queuedOn c t = true ∧ schedKeyView pre t = schedKeyView post t ∧
        candidacyNotGained pre post t) ∧
  post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c ∧
  (∀ t, post.scheduler.currentOnCore c = some t → schedKeyNotWeakened pre post t)

/-- The step `pre → post` on executing core `e` covers every remote core: each
one's flag is up afterwards, or its decision was not staled. -/
def reschedulePendingCovers (e : CoreId) (pre post : SystemState) : Prop :=
  ∀ c, c ≠ e →
    post.scheduler.reschedulePendingOnCore c = true ∨ coreDecisionUnstaled pre post c

/-- No remote flag is lowered by `st → st'` (only a core's own scheduling point
clears its flag, and on the syscall path that core is the executing one). -/
def reschedulePendingMonotone (e : CoreId) (st st' : SystemState) : Prop :=
  ∀ c, c ≠ e → st.scheduler.reschedulePendingOnCore c = true →
    st'.scheduler.reschedulePendingOnCore c = true

/-- WS-ZA ZA6.8: **the step makes no thread current on a remote core**: every
core other than the executing core `e` keeps its current thread or loses it.
A thread becomes current only through a scheduling point, and only the
executing core's own scheduling point runs (a remote deschedule empties the
remote slot and raises its flag); this is the cross-core frame that keeps a
remote core's current thread one the pre-state already ran there. -/
def currentKeptOffCore (e : CoreId) (pre post : SystemState) : Prop :=
  ∀ c, c ≠ e → ∀ t, post.scheduler.currentOnCore c = some t →
    pre.scheduler.currentOnCore c = some t

theorem currentKeptOffCore_refl (e : CoreId) (st : SystemState) : currentKeptOffCore e st st :=
  fun _ _ _ h => h

theorem currentKeptOffCore_trans {e : CoreId} {a b d : SystemState}
    (h₁ : currentKeptOffCore e a b) (h₂ : currentKeptOffCore e b d) : currentKeptOffCore e a d :=
  fun c hc t h => h₁ c hc t (h₂ c hc t h)

/-- A step that keeps every remote current slot keeps it. -/
theorem currentKeptOffCore_of_eq {e : CoreId} {pre post : SystemState}
    (h : ∀ c, c ≠ e → post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c) :
    currentKeptOffCore e pre post :=
  fun c hc _ ht => (h c hc).symm.trans ht

/-- WS-ZA ZA6.10: **the step makes no thread resident on a remote core**: every
core other than the executing core `e` keeps its resident thread or loses it.
A core's resident thread (`MachineState.residentOnCore`) is recorded only by
that core's own residency settle at its entry's tail; a final delete's core
release only clears one.  With `currentKeptOffCore` this is the cross-core
frame that keeps a remote core's resident thread one the pre-state already
held there. -/
def residentKeptOffCore (e : CoreId) (pre post : SystemState) : Prop :=
  ∀ c, c ≠ e → ∀ t, post.machine.residentOnCore c = some t →
    pre.machine.residentOnCore c = some t

theorem residentKeptOffCore_refl (e : CoreId) (st : SystemState) : residentKeptOffCore e st st :=
  fun _ _ _ h => h

theorem residentKeptOffCore_trans {e : CoreId} {a b d : SystemState}
    (h₁ : residentKeptOffCore e a b) (h₂ : residentKeptOffCore e b d) : residentKeptOffCore e a d :=
  fun c hc t h => h₁ c hc t (h₂ c hc t h)

/-- The register-bank and FP-owner writes leave the residency record alone
(`resident_frame` closes the record's equation through them by `simp`). -/
@[simp] theorem MachineState.setRegsOnCore_residentCode (ms : MachineState) (c : CoreId)
    (v : RegisterFile) : (ms.setRegsOnCore c v).residentCode = ms.residentCode := rfl
@[simp] theorem MachineState.modifyRegsOnCore_residentCode (ms : MachineState) (c : CoreId)
    (f : RegisterFile → RegisterFile) :
    (ms.modifyRegsOnCore c f).residentCode = ms.residentCode := rfl
@[simp] theorem MachineState.setFpOwnerOnCore_residentCode (ms : MachineState) (c : CoreId)
    (t? : Option SeLe4n.ThreadId) : (ms.setFpOwnerOnCore c t?).residentCode = ms.residentCode := rfl

/-- The idle dispatch and the idle fallback write a register bank and core
slots, never a residency record. -/
@[simp] theorem dispatchIdleOnCore_residentCode (st : SystemState) (c : CoreId) :
    (dispatchIdleOnCore st c).machine.residentCode = st.machine.residentCode := by
  simp [dispatchIdleOnCore]

@[simp] theorem idleFallbackOnCore_residentCode (st : SystemState) (c : CoreId) :
    (idleFallbackOnCore st c).machine.residentCode = st.machine.residentCode := by
  unfold idleFallbackOnCore; split
  · exact dispatchIdleOnCore_residentCode st c
  · rfl

@[simp] theorem saveOutgoingContextOnCore_residentCode (st : SystemState) (c : CoreId) :
    (saveOutgoingContextOnCore st c).machine.residentCode = st.machine.residentCode := by
  unfold saveOutgoingContextOnCore; split
  · rfl
  · rw [SystemState.updateTcb_machine]

/-- A step that keeps every core's residency record keeps it. -/
theorem residentKeptOffCore_of_eq {e : CoreId} {pre post : SystemState}
    (h : post.machine.residentCode = pre.machine.residentCode) :
    residentKeptOffCore e pre post :=
  fun _ _ _ ht => by unfold MachineState.residentOnCore at ht ⊢; rw [← h]; exact ht

/-- The object writes set no core's resident thread (`resident_frame`), through
any run-queue, key-hook or reschedule-flag write around them. -/
macro_rules | `(tactic| resident_frame) => `(tactic|
  (simp [SystemState.rewriteObject_machine, SystemState.updateTcb_machine,
    SystemState.updateSchedContext_machine]; done))

/-- ...and through the branches of a step's body, case by case. -/
macro_rules | `(tactic| resident_frame) => `(tactic|
  ((repeat' split) <;> (simp [SystemState.rewriteObject_machine, SystemState.updateTcb_machine,
    SystemState.updateSchedContext_machine]) <;> done))

@[simp] theorem sliceExpireOnCore_residentCode (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) :
    (sliceExpireOnCore st c tid tcb hTcb).machine.residentCode = st.machine.residentCode := by
  simp [sliceExpireOnCore, SystemState.rewriteObject_machine]

/-- Closes `post.machine = pre.machine` along a chain of writes that keep the
machine: each step is a write named in the context's successful-step
hypotheses (`h : op … st = .ok …`) or a write the goal names, its own machine
equation composed by transitivity.  The arm files register their writes'
equations with further `macro_rules`. -/
syntax "machine_chain" : tactic

macro_rules | `(tactic| machine_chain) => `(tactic| rfl)
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine Eq.trans (by assumption) ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (storeObject_machine_eq _ _ _ _ (by assumption)).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (markKeyChangeFrom_machine _ _ _).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (markKeyChangeFor_machine _ _ _).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (SystemState.updateTcb_machine _ _ _).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (SystemState.updateSchedContext_machine _ _ _).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (SystemState.rewriteObject_machine _ _ _ _).trans ?_; machine_chain))

/-- ...and along a chain of machine-keeping writes (`machine_chain`). -/
macro_rules | `(tactic| resident_frame) => `(tactic|
  (apply congrArg MachineState.residentCode; machine_chain))

/-- Closes `residentKeptOffCore e pre post` for a step that writes no core's
residency record (`resident_frame` on the record's equation). -/
macro "resident_kept" : tactic =>
  `(tactic| first
    | exact residentKeptOffCore_refl _ _
    | exact residentKeptOffCore_of_eq (by resident_frame))

/-- Recording the executing core's resident thread keeps every other core's. -/
theorem residentKeptOffCore_of_setResidentOnCore {e : CoreId} {pre post : SystemState}
    {t? : Option SeLe4n.ThreadId} (h : post.machine = pre.machine.setResidentOnCore e t?) :
    residentKeptOffCore e pre post :=
  fun c hc _ ht => by
    rw [h, MachineState.residentOnCore_setResidentOnCore_ne _ e c _ (Ne.symm hc)] at ht; exact ht

/-- WS-ZA ZA6.21: **the step erases the TCB of no remote core's resident**:
every thread resident on a core other than the executing core `e` after the
step, which had a TCB before it, still has one.  A TCB leaves the store only
through the final retire, which admits a thread resident on no core
(`threadRetirable`); with `residentKeptOffCore` this is the cross-core frame
that keeps every core's resident thread resolving to a TCB
(`SystemState.residentsHaveTcbs`). -/
def residentTcbKeptOffCore (e : CoreId) (pre post : SystemState) : Prop :=
  ∀ c, c ≠ e → ∀ t, post.machine.residentOnCore c = some t →
    (pre.getTcb? t).isSome → (post.getTcb? t).isSome

theorem residentTcbKeptOffCore_refl (e : CoreId) (st : SystemState) :
    residentTcbKeptOffCore e st st :=
  fun _ _ _ _ h => h

/-- The frame composes: a remote resident after the second step was resident
there after the first (the second step's `residentKeptOffCore`). -/
theorem residentTcbKeptOffCore_trans {e : CoreId} {a b d : SystemState}
    (h₁ : residentTcbKeptOffCore e a b) (h₂ : residentTcbKeptOffCore e b d)
    (hR : residentKeptOffCore e b d) : residentTcbKeptOffCore e a d :=
  fun c hc t ht hT => h₂ c hc t ht (h₁ c hc t (hR c hc t ht) hT)

/-- A step that keeps every TCB a TCB keeps it. -/
theorem residentTcbKeptOffCore_of_present {e : CoreId} {pre post : SystemState}
    (h : ∀ t, (pre.getTcb? t).isSome → (post.getTcb? t).isSome) :
    residentTcbKeptOffCore e pre post :=
  fun _ _ t _ hT => h t hT

/-- WS-ZA ZA6.13: **the step writes no remote core's register bank**: every
core other than the executing core `e` holds the register file it held.  A
core's bank (`MachineState.regsOnCore`) is written only by that core's own
entry: its trap-frame save, its caller's return staging and its scheduling
point's restore.  With `currentKeptOffCore` this is the half of a remote core's
bank match (`contextMatchesCurrentOnCore`) that its bank supplies; the other
half is the remote current thread's saved registers. -/
def banksKeptOffCore (e : CoreId) (pre post : SystemState) : Prop :=
  ∀ c, c ≠ e → post.machine.regsOnCore c = pre.machine.regsOnCore c

theorem banksKeptOffCore_refl (e : CoreId) (st : SystemState) : banksKeptOffCore e st st :=
  fun _ _ => rfl

theorem banksKeptOffCore_trans {e : CoreId} {a b d : SystemState}
    (h₁ : banksKeptOffCore e a b) (h₂ : banksKeptOffCore e b d) : banksKeptOffCore e a d :=
  fun c hc => (h₂ c hc).trans (h₁ c hc)

/-- The residency-record and FP-owner writes leave every bank alone
(`bank_frame` closes the banks' equation through them by `simp`). -/
@[simp] theorem MachineState.setResidentOnCore_coreRegs (ms : MachineState) (c : CoreId)
    (t? : Option SeLe4n.ThreadId) : (ms.setResidentOnCore c t?).coreRegs = ms.coreRegs := rfl
@[simp] theorem MachineState.setFpOwnerOnCore_coreRegs (ms : MachineState) (c : CoreId)
    (t? : Option SeLe4n.ThreadId) : (ms.setFpOwnerOnCore c t?).coreRegs = ms.coreRegs := rfl

@[simp] theorem saveOutgoingContextOnCore_coreRegs (st : SystemState) (c : CoreId) :
    (saveOutgoingContextOnCore st c).machine.coreRegs = st.machine.coreRegs := by
  unfold saveOutgoingContextOnCore; split
  · rfl
  · rw [SystemState.updateTcb_machine]

@[simp] theorem sliceExpireOnCore_coreRegs (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) :
    (sliceExpireOnCore st c tid tcb hTcb).machine.coreRegs = st.machine.coreRegs := by
  simp [sliceExpireOnCore, SystemState.rewriteObject_machine]

/-- A step that keeps every core's bank keeps it. -/
theorem banksKeptOffCore_of_eq {e : CoreId} {pre post : SystemState}
    (h : post.machine.coreRegs = pre.machine.coreRegs) : banksKeptOffCore e pre post :=
  fun _ _ => by unfold MachineState.regsOnCore; rw [h]

/-- Writing the executing core's bank keeps every other core's. -/
theorem banksKeptOffCore_of_setRegsOnCore {e : CoreId} {pre post : SystemState}
    {v : SeLe4n.RegisterFile} (h : post.machine.coreRegs = (pre.machine.setRegsOnCore e v).coreRegs) :
    banksKeptOffCore e pre post :=
  fun c hc => by
    have := MachineState.regsOnCore_setRegsOnCore_ne pre.machine e c v (Ne.symm hc)
    unfold MachineState.regsOnCore at this ⊢; rw [h]; exact this

/-- Closes `post.machine.coreRegs = pre.machine.coreRegs` for a step that writes
no core's register bank: by definition, from a hypothesis that equates the
machines, through the object writes by `simp`, case by case through a step's
branches, or along a chain of machine-keeping writes (`machine_chain`).  The arm
files register further alternatives with `macro_rules`. -/
syntax "bank_frame" : tactic

macro_rules | `(tactic| bank_frame) => `(tactic|
  (first
    | rfl
    | assumption
    | exact congrArg MachineState.coreRegs (by assumption)
    | (rw [‹SystemState.machine _ = _›])
    | (simp [SystemState.rewriteObject_machine, SystemState.updateTcb_machine,
        SystemState.updateSchedContext_machine]; done)
    | (simp_all only [SystemState.machine]; done)))
macro_rules | `(tactic| bank_frame) => `(tactic|
  ((repeat' split) <;> (simp [SystemState.rewriteObject_machine, SystemState.updateTcb_machine,
    SystemState.updateSchedContext_machine]) <;> done))
macro_rules | `(tactic| bank_frame) => `(tactic|
  (apply congrArg MachineState.coreRegs; machine_chain))

/-- The idle dispatch and the idle fallback write the bank of the core they
dispatch, and no other. -/
@[simp] theorem dispatchIdleOnCore_regsOnCore_ne (st : SystemState) (c d : CoreId) (h : c ≠ d) :
    (dispatchIdleOnCore st c).machine.regsOnCore d = st.machine.regsOnCore d := by
  simp only [dispatchIdleOnCore]
  rw [restoreIncomingContextOnCore_regsOnCore_ne _ c d _ h, SystemState.runRemoveOnCore_machine]

@[simp] theorem idleFallbackOnCore_regsOnCore_ne (st : SystemState) (c d : CoreId) (h : c ≠ d) :
    (idleFallbackOnCore st c).machine.regsOnCore d = st.machine.regsOnCore d := by
  unfold idleFallbackOnCore; split
  · exact dispatchIdleOnCore_regsOnCore_ne st c d h
  · rfl

/-- Closes `banksKeptOffCore e pre post` for a step that writes no core's bank
(`bank_frame` on the banks' equation), or only the executing core's (`simp`
through the bank writes' frames, case by case).  The arm files register further
alternatives with `macro_rules`. -/
syntax "bank_kept" : tactic

macro_rules | `(tactic| bank_kept) => `(tactic|
  (first
    | exact banksKeptOffCore_refl _ _
    | (apply banksKeptOffCore_of_eq; bank_frame)
    | (intro _c hc; have hc' := Ne.symm hc;
       simp [hc, hc', SystemState.rewriteObject_machine,
         SystemState.updateTcb_machine, SystemState.updateSchedContext_machine,
         restoreIncomingContextOnCore_regsOnCore_ne,
         restoreIncomingContextOnCoreUnlessCurrent_regsOnCore_ne,
         MachineState.regsOnCore_setRegsOnCore_ne]; done)
    | (intro _c hc; have hc' := Ne.symm hc;
       (repeat' split) <;> (simp [hc, hc', SystemState.rewriteObject_machine,
         SystemState.updateTcb_machine, SystemState.updateSchedContext_machine,
         restoreIncomingContextOnCore_regsOnCore_ne,
         restoreIncomingContextOnCoreUnlessCurrent_regsOnCore_ne,
         MachineState.regsOnCore_setRegsOnCore_ne]) <;> done)))

/-! ### Composition laws -/

theorem schedKeyNotWeakened_refl (st : SystemState) (t : SeLe4n.ThreadId) :
    schedKeyNotWeakened st st t :=
  fun kq h => ⟨kq, h, Nat.le_refl _, Nat.le_refl _, rfl⟩

theorem schedKeyNotWeakened_trans {a b c : SystemState} {t : SeLe4n.ThreadId}
    (h₁ : schedKeyNotWeakened a b t) (h₂ : schedKeyNotWeakened b c t) :
    schedKeyNotWeakened a c t := by
  intro kq hq
  obtain ⟨kb, hb, hb1, hb2, hb3⟩ := h₂ kq hq
  obtain ⟨ka, ha, ha1, ha2, ha3⟩ := h₁ kb hb
  exact ⟨ka, ha, Nat.le_trans ha1 hb1, Nat.le_trans hb2 ha2, hb3.trans ha3⟩

theorem schedKeyNotWeakened_of_eq {pre post : SystemState} {t : SeLe4n.ThreadId}
    (h : schedKeyView pre t = schedKeyView post t) : schedKeyNotWeakened pre post t :=
  fun kq hq => ⟨kq, h.trans hq, Nat.le_refl _, Nat.le_refl _, rfl⟩

theorem candidacyNotGained_refl (st : SystemState) (t : SeLe4n.ThreadId) :
    candidacyNotGained st st t := id

theorem candidacyNotGained_trans {a b c : SystemState} {t : SeLe4n.ThreadId}
    (h₁ : candidacyNotGained a b t) (h₂ : candidacyNotGained b c t) :
    candidacyNotGained a c t := fun h => h₁ (h₂ h)

theorem candidacyNotGained_of_eq {pre post : SystemState} {t : SeLe4n.ThreadId}
    (h : budgetEligibleView pre t = budgetEligibleView post t) :
    candidacyNotGained pre post t := fun hq => h.trans hq

/-- No thread gains candidacy when every binding stays put and no context's
budget goes from empty to positive. -/
theorem candidacyNotGained_of_budget_mono {pre post : SystemState}
    (hT : ∀ t, (post.getTcb? t).map TCB.schedContextBinding =
      (pre.getTcb? t).map TCB.schedContextBinding)
    (hSc : ∀ sc, (post.getSchedContext? sc).map (·.budgetRemaining.isPositive) = some true →
      (pre.getSchedContext? sc).map (·.budgetRemaining.isPositive) = some true)
    (t : SeLe4n.ThreadId) : candidacyNotGained pre post t := by
  intro h
  have hB := hT t
  unfold budgetEligibleView at h ⊢
  cases hq : post.getTcb? t with
  | none => rw [hq] at h; cases h
  | some b =>
    cases hp : pre.getTcb? t with
    | none => rw [hq, hp] at hB; cases hB
    | some a =>
      rw [hq, hp] at hB
      rw [hq] at h
      simp only [Option.map_some, Option.some.injEq] at hB h ⊢
      unfold hasSufficientBudget at h ⊢
      rw [hB] at h
      cases hA : a.schedContextBinding with
      | unbound => rfl
      | bound sc =>
        rw [hA] at h; simp only at h ⊢
        have := hSc sc
        cases hq' : post.getSchedContext? sc <;> cases hp' : pre.getSchedContext? sc <;>
          simp_all
      | donated sc o =>
        rw [hA] at h; simp only at h ⊢
        have := hSc sc
        cases hq' : post.getSchedContext? sc <;> cases hp' : pre.getSchedContext? sc <;>
          simp_all

theorem coreDecisionUnstaled_refl (st : SystemState) (c : CoreId) :
    coreDecisionUnstaled st st c :=
  ⟨fun _ h => ⟨h, rfl, candidacyNotGained_refl st _⟩, rfl, fun t _ => schedKeyNotWeakened_refl st t⟩

theorem coreDecisionUnstaled_trans {a b d : SystemState} {c : CoreId}
    (h₁ : coreDecisionUnstaled a b c) (h₂ : coreDecisionUnstaled b d c) :
    coreDecisionUnstaled a d c := by
  obtain ⟨hq₁, hc₁, hw₁⟩ := h₁
  obtain ⟨hq₂, hc₂, hw₂⟩ := h₂
  refine ⟨fun t ht => ?_, hc₂.trans hc₁, fun t ht => ?_⟩
  · obtain ⟨hb, hk₂, hg₂⟩ := hq₂ t ht
    obtain ⟨ha, hk₁, hg₁⟩ := hq₁ t hb
    exact ⟨ha, hk₁.trans hk₂, candidacyNotGained_trans hg₁ hg₂⟩
  · exact schedKeyNotWeakened_trans (hw₁ t (hc₂ ▸ ht)) (hw₂ t ht)

theorem reschedulePendingCovers_refl (e : CoreId) (st : SystemState) :
    reschedulePendingCovers e st st :=
  fun c _ => Or.inr (coreDecisionUnstaled_refl st c)

theorem reschedulePendingMonotone_refl (e : CoreId) (st : SystemState) :
    reschedulePendingMonotone e st st :=
  fun _ _ h => h

theorem reschedulePendingMonotone_trans {e : CoreId} {a b d : SystemState}
    (h₁ : reschedulePendingMonotone e a b) (h₂ : reschedulePendingMonotone e b d) :
    reschedulePendingMonotone e a d :=
  fun c hc h => h₂ c hc (h₁ c hc h)

/-- Coverage composes: a step that covers every remote core, followed by one
that covers it and lowers no remote flag, covers it end to end. -/
theorem reschedulePendingCovers_trans {e : CoreId} {a b d : SystemState}
    (h₁ : reschedulePendingCovers e a b) (h₂ : reschedulePendingCovers e b d)
    (hMono : reschedulePendingMonotone e b d) :
    reschedulePendingCovers e a d := by
  intro c hc
  rcases h₂ c hc with hFlag | hU₂
  · exact Or.inl hFlag
  · rcases h₁ c hc with hFlag | hU₁
    · exact Or.inl (hMono c hc hFlag)
    · exact Or.inr (coreDecisionUnstaled_trans hU₁ hU₂)

/-! ### The bridge to the commit diff -/

/-- The key view of a stored TCB, spelled out. -/
theorem schedKeyView_of_getTcb {st : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    (h : st.getTcb? t = some tcb) :
    schedKeyView st t =
      some ((effectiveSchedParams st tcb).1, (effectiveSchedParams st tcb).2.1.val,
        (effectiveSchedParams st tcb).2.2) := by
  simp [schedKeyView, h]

/-- Every object rule of the diff that fires names a remote core whose
decision the step staled.  `hId` is the store's self-identity at `oid` (a TCB
stored under `oid` is the thread `oid` names). -/
theorem crossCoreSgiBody_some_staled {pre post : SystemState} {e : CoreId} {oid : SeLe4n.ObjId}
    {c : CoreId} {k : SgiKind}
    (hId : ∀ tcb : TCB, post.getObject? oid = some (.tcb tcb) → tcb.tid.toObjId = oid)
    (h : crossCoreSgiBody pre post e oid = some (c, k)) :
    c ≠ e ∧ ¬ coreDecisionUnstaled pre post c := by
  unfold crossCoreSgiBody at h
  split at h
  next tpost hPost =>
    have hTid : tpost.tid.toObjId = oid := hId tpost hPost
    have hPostTcb : post.getTcb? tpost.tid = some tpost := by
      unfold SystemState.getTcb?
      rw [hTid]
      simp only [SystemState.getObject?] at hPost
      rw [hPost]
    split at h
    next tpre hPre =>
      dsimp only at h
      split at h
      next hQ =>
        split at h
        · exact absurd h (by simp)
        next hNotExec =>
          split at h
          · exact absurd h (by simp)
          next hFire =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            refine ⟨by simpa using hNotExec, fun hU => hFire ?_⟩
            obtain ⟨hIn, hKey, -⟩ := hU.1 _ hQ
            rw [schedKeyView_of_getTcb hPre, schedKeyView_of_getTcb hPostTcb] at hKey
            simp only [Option.some.injEq, Prod.mk.injEq] at hKey
            simp [hIn, hKey.1, hKey.2.1, hKey.2.2]
      next hNotQ =>
        split at h
        next preCur hFind =>
          have hPreCur : pre.scheduler.currentOnCore preCur = some tpost.tid := by
            simpa using List.find?_some hFind
          split at h
          · exact absurd h (by simp)
          next hNotExec =>
            split at h
            next hDesched =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              refine ⟨by simpa using hNotExec, fun hU => ?_⟩
              have : post.scheduler.currentOnCore preCur = some tpost.tid := hU.2.1.trans hPreCur
              simp [this] at hDesched
            next hStill =>
              have hPostCur : post.scheduler.currentOnCore preCur = some tpost.tid := by
                simpa using hStill
              split at h
              next hWeak =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, -⟩ := h
                refine ⟨by simpa using hNotExec, fun hU => ?_⟩
                obtain ⟨kp, hkp, h1, h2, h3⟩ := hU.2.2 _ hPostCur _
                  (schedKeyView_of_getTcb hPostTcb)
                rw [schedKeyView_of_getTcb hPre] at hkp
                simp only [Option.some.injEq] at hkp
                subst hkp
                simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hWeak
                simp only at h1 h2 h3
                rcases hWeak with (hw | hw) | hw
                · omega
                · omega
                · exact hw h3.symm
              · exact absurd h (by simp)
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The slot rule fires only on a remote core whose current slot changed, which
stales it. -/
theorem currentSlotChangeSgis_staled {pre post : SystemState} {e c : CoreId} {k : SgiKind}
    (h : (c, k) ∈ currentSlotChangeSgis pre post e) :
    c ≠ e ∧ ¬ coreDecisionUnstaled pre post c := by
  obtain ⟨hne, hChanged⟩ :=
    PriorityInheritance.currentSlotChangeSgis_not_execCore pre post e c k h
  exact ⟨hne, fun hU => hChanged hU.2.1⟩

/-- **The diff's cores are flagged.**  On a covering step, every core the
whole-index diff names has its reschedule flag up in the post-state.  `hId` is
the post-state store's self-identity (each stored TCB is the thread its slot
names). -/
theorem computeCrossCoreSgis_core_flagged_of_covers {e : CoreId} {pre post : SystemState}
    (hId : ∀ oid (tcb : TCB), post.getObject? oid = some (.tcb tcb) → tcb.tid.toObjId = oid)
    (hCov : reschedulePendingCovers e pre post)
    {c : CoreId} {k : SgiKind} (hMem : (c, k) ∈ computeCrossCoreSgis pre post e) :
    post.scheduler.reschedulePendingOnCore c = true := by
  have hSub := Concurrency.dedupCrossCoreSgis_subset _ (c, k) hMem
  have hStaled : c ≠ e ∧ ¬ coreDecisionUnstaled pre post c := by
    rcases List.mem_append.mp hSub with hObj | hSlot
    · obtain ⟨oid, -, hBody⟩ := List.mem_filterMap.mp hObj
      exact crossCoreSgiBody_some_staled (hId oid) hBody
    · exact currentSlotChangeSgis_staled hSlot
  rcases hCov c hStaled.1 with hFlag | hU
  · exact hFlag
  · exact absurd hU hStaled.2

/-- **What the commit's switch needs.**  On a covering step, every core the diff
names is named by the flag-derived list, unless its flag was already up before
the step (its SGI is outstanding). -/
theorem computeCrossCoreSgis_mem_flags_of_covers {e : CoreId} {pre post : SystemState}
    (hId : ∀ oid (tcb : TCB), post.getObject? oid = some (.tcb tcb) → tcb.tid.toObjId = oid)
    (hCov : reschedulePendingCovers e pre post)
    {c : CoreId} {k : SgiKind} (hMem : (c, k) ∈ computeCrossCoreSgis pre post e) :
    (c, SgiKind.reschedule) ∈
        rescheduleSgisFromFlags pre.scheduler.reschedulePending
          post.scheduler.reschedulePending ∨
      pre.scheduler.reschedulePendingOnCore c = true := by
  have hFlag := computeCrossCoreSgis_core_flagged_of_covers hId hCov hMem
  cases hPre : pre.scheduler.reschedulePendingOnCore c
  · left
    rw [mem_rescheduleSgisFromFlags_iff]
    exact ⟨rfl, hPre, hFlag⟩
  · exact Or.inr rfl

/-! ### Key frames -/

/-- A TCB rewrite that keeps the five fields the effective key reads. -/
def schedKeyFieldsEq (a b : TCB) : Prop :=
  b.priority = a.priority ∧ b.deadline = a.deadline ∧
    b.schedContextBinding = a.schedContextBinding ∧ b.pipBoost = a.pipBoost ∧
    b.domain = a.domain

theorem schedKeyFieldsEq_ipcState (a : TCB) (s : ThreadIpcState) :
    schedKeyFieldsEq a (a.setIpcState s) := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The effective key reads only the key fields and the scheduling contexts. -/
theorem resolveEffectivePrioDeadline_congr {st st' : SystemState} {a b : TCB}
    (hSc : ∀ sc, st'.getSchedContext? sc = st.getSchedContext? sc)
    (hK : schedKeyFieldsEq a b) :
    resolveEffectivePrioDeadline st' b = resolveEffectivePrioDeadline st a := by
  obtain ⟨hP, hD, hB, hPip, -⟩ := hK
  unfold resolveEffectivePrioDeadline
  rw [hP, hD, hB, hPip]
  cases a.schedContextBinding <;> simp only [hSc]

/-- The full key agrees when the two-component key and the domain do. -/
theorem effectiveSchedParams_eq_of {st st' : SystemState} {a b : TCB}
    (hR : resolveEffectivePrioDeadline st' b = resolveEffectivePrioDeadline st a)
    (hDom : b.domain = a.domain) :
    effectiveSchedParams st' b = effectiveSchedParams st a := by
  have h1 := effectiveSchedParams_priority_deadline_eq_resolve st' b
  have h2 := effectiveSchedParams_priority_deadline_eq_resolve st a
  rw [hR, ← h2] at h1
  have hd : (effectiveSchedParams st' b).2.2 = (effectiveSchedParams st a).2.2 :=
    (effectiveSchedParams_domain_eq st' b).trans
      (hDom.trans (effectiveSchedParams_domain_eq st a).symm)
  revert h1 hd
  generalize effectiveSchedParams st' b = x
  generalize effectiveSchedParams st a = y
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  simp only [Prod.mk.injEq]
  rintro ⟨rfl, rfl⟩ rfl
  exact ⟨rfl, rfl, rfl⟩

/-- The full key reads only the key fields and the scheduling contexts. -/
theorem effectiveSchedParams_congr {st st' : SystemState} {a b : TCB}
    (hSc : ∀ sc, st'.getSchedContext? sc = st.getSchedContext? sc)
    (hK : schedKeyFieldsEq a b) :
    effectiveSchedParams st' b = effectiveSchedParams st a :=
  effectiveSchedParams_eq_of (resolveEffectivePrioDeadline_congr hSc hK) hK.2.2.2.2

/-- Budget eligibility reads the binding and the contexts' budget signs alone. -/
theorem hasSufficientBudget_congr {st st' : SystemState} {a b : TCB}
    (hSc : ∀ sc, (st'.getSchedContext? sc).map (·.budgetRemaining.isPositive) =
      (st.getSchedContext? sc).map (·.budgetRemaining.isPositive))
    (hB : b.schedContextBinding = a.schedContextBinding) :
    hasSufficientBudget st' b = hasSufficientBudget st a := by
  unfold hasSufficientBudget
  rw [hB]
  cases a.schedContextBinding with
  | unbound => rfl
  | bound sc =>
    have := hSc sc
    cases hq : st'.getSchedContext? sc <;> cases hp : st.getSchedContext? sc <;> simp_all
  | donated sc o =>
    have := hSc sc
    cases hq : st'.getSchedContext? sc <;> cases hp : st.getSchedContext? sc <;> simp_all

/-- The scheduler record is not read by budget eligibility. -/
@[simp] theorem budgetEligibleView_scheduler (st : SystemState) (s : SchedulerState)
    (t : SeLe4n.ThreadId) :
    budgetEligibleView { st with scheduler := s } t = budgetEligibleView st t := rfl

/-- Budget eligibility reads the object store alone. -/
theorem budgetEligibleView_of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects)
    (t : SeLe4n.ThreadId) : budgetEligibleView st' t = budgetEligibleView st t := by
  have hT : st'.getTcb? t = st.getTcb? t := by unfold SystemState.getTcb?; rw [h]
  have hS : hasSufficientBudget st' = hasSufficientBudget st := funext fun _ =>
    hasSufficientBudget_congr (fun sc => by unfold SystemState.getSchedContext?; rw [h]) rfl
  unfold budgetEligibleView; rw [hT, hS]

/-- WS-ZA ZA4.5: the run-queue links are no thread's budget eligibility. -/
theorem budgetEligibleView_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffRunLinks st) (t : SeLe4n.ThreadId) :
    budgetEligibleView st' t = budgetEligibleView st t := by
  have hS : hasSufficientBudget st' = hasSufficientBudget st := funext fun _ =>
    hasSufficientBudget_congr (fun sc => by rw [h.getSchedContext?]) rfl
  unfold budgetEligibleView
  rw [hS]
  exact TCB.map_proj_eq_of_map_withoutRunLinks_eq (hasSufficientBudget st) (h.getTcb? t)

/-- A TCB rewrite that keeps the binding moves no thread's budget eligibility. -/
theorem budgetEligibleView_rewriteObject_tcb {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb t' : TCB} (hOld : st.getTcb? tid = some tcb)
    (h : st.rewriteAdmissible tid.toObjId (.tcb t')) (hInv : st.objects.invExt)
    (hB : t'.schedContextBinding = tcb.schedContextBinding) (t : SeLe4n.ThreadId) :
    budgetEligibleView (st.rewriteObject tid.toObjId (.tcb t') h) t = budgetEligibleView st t := by
  have hSc := SystemState.rewriteObject_tcb_getSchedContext? st tid.toObjId t' h hInv
  have hS : ∀ a b : TCB, b.schedContextBinding = a.schedContextBinding →
      hasSufficientBudget (st.rewriteObject tid.toObjId (.tcb t') h) b =
        hasSufficientBudget st a :=
    fun a b hab => hasSufficientBudget_congr (fun sc => by rw [hSc]) hab
  by_cases hEq : t = tid
  · subst hEq
    unfold budgetEligibleView
    rw [SystemState.rewriteObject_tcb_getTcb?_self st t t' h hInv, hOld]
    simp only [Option.map_some, hS tcb t' hB]
  · have hNe : tid.toObjId ≠ t.toObjId :=
      fun h' => hEq (SeLe4n.ThreadId.toObjId_injective _ _ h').symm
    unfold budgetEligibleView
    rw [SystemState.rewriteObject_getTcb?_ne st _ _ h hInv t hNe]
    cases st.getTcb? t with
    | none => rfl
    | some x => simp only [Option.map_some, hS x x rfl]

/-- The scheduler record is not read by the key. -/
@[simp] theorem schedKeyView_scheduler (st : SystemState) (s : SchedulerState)
    (t : SeLe4n.ThreadId) :
    schedKeyView { st with scheduler := s } t = schedKeyView st t := rfl

/-- WS-ZA ZA4.5: the run-queue links are no thread's key. -/
theorem schedKeyView_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffRunLinks st) (t : SeLe4n.ThreadId) :
    schedKeyView st' t = schedKeyView st t := by
  unfold schedKeyView
  simp only [effectiveSchedParams_of_objectsAgreeOffRunLinks st st' _ h]
  exact TCB.map_proj_eq_of_map_withoutRunLinks_eq (fun tcb =>
    ((effectiveSchedParams st tcb).1, (effectiveSchedParams st tcb).2.1.val,
      (effectiveSchedParams st tcb).2.2)) (h.getTcb? t)

/-- A key-preserving TCB rewrite moves no thread's key. -/
theorem schedKeyView_rewriteObject_tcb {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb t' : TCB} (hOld : st.getTcb? tid = some tcb)
    (h : st.rewriteAdmissible tid.toObjId (.tcb t')) (hInv : st.objects.invExt)
    (hK : schedKeyFieldsEq tcb t') (t : SeLe4n.ThreadId) :
    schedKeyView (st.rewriteObject tid.toObjId (.tcb t') h) t = schedKeyView st t := by
  have hSc := SystemState.rewriteObject_tcb_getSchedContext? st tid.toObjId t' h hInv
  by_cases hEq : t = tid
  · subst hEq
    unfold schedKeyView
    rw [SystemState.rewriteObject_tcb_getTcb?_self st t t' h hInv, hOld]
    simp only [Option.map_some, effectiveSchedParams_congr hSc hK]
  · have hNe : tid.toObjId ≠ t.toObjId :=
      fun h' => hEq (SeLe4n.ThreadId.toObjId_injective _ _ h').symm
    unfold schedKeyView
    rw [SystemState.rewriteObject_getTcb?_ne st _ _ h hInv t hNe]
    cases st.getTcb? t with
    | none => rfl
    | some x => simp only [Option.map_some, effectiveSchedParams_congr hSc
                  (⟨rfl, rfl, rfl, rfl, rfl⟩ : schedKeyFieldsEq x x)]

/-! ### Coverage from frames -/

/-- A core whose slots are untouched and whose threads' keys did not move is
unstaled. -/
theorem coreDecisionUnstaled_of_frame {pre post : SystemState} {c : CoreId}
    (hKeys : ∀ t, schedKeyView post t = schedKeyView pre t)
    (hElig : ∀ t, budgetEligibleView post t = budgetEligibleView pre t)
    (hRq : ∀ t, post.queuedOn c t = true → pre.queuedOn c t = true)
    (hCur : post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c) :
    coreDecisionUnstaled pre post c :=
  ⟨fun t ht => ⟨hRq t ht, (hKeys t).symm, candidacyNotGained_of_eq (hElig t).symm⟩, hCur,
   fun t _ => schedKeyNotWeakened_of_eq (hKeys t).symm⟩

/-- A key-framing step covers every core it flags or leaves slot-unchanged
(a run queue may only shrink). -/
theorem reschedulePendingCovers_of_frame {e : CoreId} {pre post : SystemState}
    (hKeys : ∀ t, schedKeyView post t = schedKeyView pre t)
    (hElig : ∀ t, budgetEligibleView post t = budgetEligibleView pre t)
    (hSlots : ∀ c, c ≠ e → post.scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, post.queuedOn c t = true → pre.queuedOn c t = true) ∧
        post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c)) :
    reschedulePendingCovers e pre post := fun c hc =>
  (hSlots c hc).imp id fun ⟨hRq, hCur⟩ => coreDecisionUnstaled_of_frame hKeys hElig hRq hCur

/-! ### The run-queue primitives -/

/-- The wake covers: it flags the core it inserts on and moves no key (the
woken TCB's rewrite only marks it `.ready`). -/
theorem enqueueRunnableOnCore_covers (e c : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    reschedulePendingCovers e st (enqueueRunnableOnCore st c tid) := by
  cases hTcb : st.getTcb? tid with
  | none =>
    rw [enqueueRunnableOnCore_no_tcb_noop st c tid hTcb]; exact reschedulePendingCovers_refl e st
  | some tcb =>
    cases hFresh : wakeDeclines st c tid with
    | true =>
      rw [enqueueRunnableOnCore_eq_self_of_declines st c tid hFresh]
      exact reschedulePendingCovers_refl e st
    | false =>
      obtain ⟨E, hE⟩ := enqueueRunnableOnCore_scheduler_of_fresh st c tid tcb hTcb hFresh
      apply reschedulePendingCovers_of_frame
      · -- The `.ready` mark moves no key, and the run-queue links are no key.
        intro t
        exact (schedKeyView_of_objectsAgreeOffRunLinks
          (enqueueRunnableOnCore_objectsAgree_marked st c tid tcb hTcb hFresh) t).trans
          (schedKeyView_rewriteObject_tcb hTcb (SystemState.rewriteAdmissible_tcb hTcb _) hInv
            (schedKeyFieldsEq_ipcState tcb _) t)
      · intro t
        exact (budgetEligibleView_of_objectsAgreeOffRunLinks
          (enqueueRunnableOnCore_objectsAgree_marked st c tid tcb hTcb hFresh) t).trans
          (budgetEligibleView_rewriteObject_tcb (t' := tcb.setIpcState .ready) hTcb
            (SystemState.rewriteAdmissible_tcb hTcb _) hInv rfl t)
      · intro c' _
        by_cases hc : c = c'
        · subst hc; left; rw [hE]; simp
        · right
          refine ⟨fun t ht => ?_, by rw [hE]; simp [hc]⟩
          rw [enqueueRunnableOnCore_queuedOn st c tid hInv] at ht
          split at ht
          · exact absurd (of_decide_eq_true ht) (Ne.symm hc)
          · exact ht

theorem enqueueRunnableOnCore_monotone (e c : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    reschedulePendingMonotone e st (enqueueRunnableOnCore st c tid) := by
  intro c' _ hF
  rcases enqueueRunnableOnCore_scheduler_cases st c tid with h | ⟨E, p, h⟩ <;> rw [h]
  · exact hF
  · by_cases hc : c = c'
    · subst hc; simp
    · simp [hc, hF]

/-- WS-ZA ZA6.8: the wake makes no thread current anywhere. -/
theorem enqueueRunnableOnCore_currentKept (e c : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) : currentKeptOffCore e st (enqueueRunnableOnCore st c tid) := by
  refine currentKeptOffCore_of_eq fun c' _ => ?_
  rcases enqueueRunnableOnCore_scheduler_cases st c tid with h | ⟨E, p, h⟩ <;> rw [h]
  simp

/-- The removal covers: a queue removal stales nothing, and clearing the
current slot raises the flag. -/
theorem removeRunnableOnCore_covers (e : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    reschedulePendingCovers e st (removeRunnableOnCore st tid c) := by
  apply reschedulePendingCovers_of_frame (fun t => schedKeyView_of_objectsAgreeOffRunLinks
    (removeRunnableOnCore_objectsAgreeOffRunLinks st tid c) t)
    (fun t => budgetEligibleView_of_objectsAgreeOffRunLinks
      (removeRunnableOnCore_objectsAgreeOffRunLinks st tid c) t)
  intro c' _
  rw [removeRunnableOnCore_scheduler]
  by_cases hc : c = c'
  · subst hc
    by_cases hcur : st.scheduler.currentOnCore c = some tid
    · left; simp [hcur]
    · right
      refine ⟨fun t ht => ?_, by simp [hcur]⟩
      rw [removeRunnableOnCore_queuedOn] at ht
      split at ht
      · exact absurd ht (by simp)
      · exact ht
  · right
    refine ⟨fun t ht => ?_, by simp [hc]⟩
    rw [removeRunnableOnCore_queuedOn] at ht
    split at ht
    · exact absurd ht (by simp)
    · exact ht

theorem removeRunnableOnCore_monotone (e : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    reschedulePendingMonotone e st (removeRunnableOnCore st tid c) := by
  intro c' _ hF
  by_cases hc : c = c'
  · subst hc; simp [removeRunnableOnCore, hF]
  · simp [removeRunnableOnCore, hc, hF]

/-- WS-ZA ZA6.8: the removal keeps every current slot or empties it. -/
theorem removeRunnableOnCore_currentKept (e : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    currentKeptOffCore e st (removeRunnableOnCore st tid c) := by
  intro c' _ t ht
  rw [removeRunnableOnCore_scheduler] at ht
  by_cases hc : c = c'
  · subst hc
    by_cases hcur : st.scheduler.currentOnCore c = some tid
    · simp [hcur] at ht
    · simpa [hcur] using ht
  · simpa [hc] using ht

/-! ### The key-change hook -/

/-- The hook writes flags only, so no key moves through it. -/
@[simp] theorem schedKeyView_markKeyChangeFor (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (t : SeLe4n.ThreadId) :
    schedKeyView (markKeyChangeFor st tid k) t = schedKeyView st t :=
  markKeyChangeFor_extract_frame (fun s => schedKeyView s t) st tid k (fun _ _ => rfl)

/-- The hook writes flags only, so no budget eligibility moves through it. -/
@[simp] theorem budgetEligibleView_markKeyChangeFor (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (t : SeLe4n.ThreadId) :
    budgetEligibleView (markKeyChangeFor st tid k) t = budgetEligibleView st t :=
  markKeyChangeFor_extract_frame (fun s => budgetEligibleView s t) st tid k (fun _ _ => rfl)

@[simp] theorem schedKeyView_markCandidacyGainFor (st : SystemState) (tid : SeLe4n.ThreadId)
    (b : Bool) (t : SeLe4n.ThreadId) :
    schedKeyView (markCandidacyGainFor st tid b) t = schedKeyView st t :=
  markCandidacyGainFor_extract_frame (fun s => schedKeyView s t) st tid b (fun _ _ => rfl)

@[simp] theorem budgetEligibleView_markCandidacyGainFor (st : SystemState)
    (tid : SeLe4n.ThreadId) (b : Bool) (t : SeLe4n.ThreadId) :
    budgetEligibleView (markCandidacyGainFor st tid b) t = budgetEligibleView st t :=
  markCandidacyGainFor_extract_frame (fun s => budgetEligibleView s t) st tid b (fun _ _ => rfl)

/-- **The candidacy hook flags a gain**: a core whose queue holds `tid`, when
`tid` was not budget-eligible on `pre` (its TCB there was `tcb`) and is on
`mid`. -/
theorem markCandidacyGainFor_reschedulePendingOnCore_of_gained {pre mid : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {c : CoreId}
    (hPre : pre.getTcb? tid = some tcb)
    (hMem : mid.queuedOn c tid = true)
    (hGain : ¬ candidacyNotGained pre mid tid) :
    (markCandidacyGainFor mid tid (hasSufficientBudget pre tcb)).scheduler.reschedulePendingOnCore c
      = true := by
  have hPost : budgetEligibleView mid tid = some true :=
    Classical.byContradiction fun h => hGain fun h' => absurd h' h
  have hPreF : hasSufficientBudget pre tcb = false := by
    cases hb : hasSufficientBudget pre tcb
    · rfl
    · exact absurd (fun _ => by simp [budgetEligibleView, hPre, hb]) hGain
  unfold budgetEligibleView at hPost
  rw [markCandidacyGainFor_reschedulePendingOnCore, hPreF, hPost, hMem]
  simp

theorem markKeyChangeFor_reschedulePendingOnCore_of_moved {pre mid : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {c : CoreId}
    (hPre : pre.getTcb? tid = some tcb)
    (hMem : mid.queuedOn c tid = true)
    (hMoved : schedKeyView mid tid ≠ schedKeyView pre tid) :
    (markKeyChangeFor mid tid (effectiveSchedParams pre tcb)).scheduler.reschedulePendingOnCore c
      = true := by
  simp only [markKeyChangeFor, markReschedulePendingWhere_reschedulePendingOnCore,
    Concurrency.mem_allCores, decide_true, Bool.and_true, hMem, Bool.and_true]
  cases hT : mid.getTcb? tid with
  | none => simp
  | some x =>
    have hNe : ¬ ((effectiveSchedParams pre tcb).1 = (effectiveSchedParams mid x).1 ∧
        (effectiveSchedParams pre tcb).2.1.val = (effectiveSchedParams mid x).2.1.val ∧
        (effectiveSchedParams pre tcb).2.2 = (effectiveSchedParams mid x).2.2) := by
      rintro ⟨h1, h2, h3⟩
      apply hMoved
      simp only [schedKeyView, hT, hPre, Option.map_some, h1, h2, h3]
    simp only [Option.map_some]
    rcases Decidable.not_and_iff_not_or_not.mp hNe with h | h
    · simp [h]
    · rcases Decidable.not_and_iff_not_or_not.mp h with h | h <;> simp [h]

theorem markKeyChangeFor_reschedulePendingOnCore_of_weakened {pre mid : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {c : CoreId}
    (hPre : pre.getTcb? tid = some tcb)
    (hCur : mid.scheduler.currentOnCore c = some tid)
    (hW : ¬ schedKeyNotWeakened pre mid tid) :
    (markKeyChangeFor mid tid (effectiveSchedParams pre tcb)).scheduler.reschedulePendingOnCore c
      = true := by
  simp only [markKeyChangeFor, markReschedulePendingWhere_reschedulePendingOnCore,
    Concurrency.mem_allCores, decide_true, Bool.and_true, hCur, beq_self_eq_true]
  cases hT : mid.getTcb? tid with
  | none =>
    exact absurd (fun kq hq => by simp [schedKeyView, hT] at hq) hW
  | some x =>
    have hLt : (effectiveSchedParams mid x).1.val < (effectiveSchedParams pre tcb).1.val ∨
        (effectiveSchedParams pre tcb).2.1.val < (effectiveSchedParams mid x).2.1.val ∨
        (effectiveSchedParams pre tcb).2.2 ≠ (effectiveSchedParams mid x).2.2 := by
      apply Classical.byContradiction
      intro hNot
      apply hW
      intro kq hq
      simp only [schedKeyView, hT, Option.map_some, Option.some.injEq] at hq
      subst hq
      refine ⟨((effectiveSchedParams pre tcb).1, (effectiveSchedParams pre tcb).2.1.val,
        (effectiveSchedParams pre tcb).2.2), by simp [schedKeyView, hPre], ?_, ?_, ?_⟩
      · exact Nat.le_of_not_lt fun h => hNot (Or.inl h)
      · exact Nat.le_of_not_lt fun h => hNot (Or.inr (Or.inl h))
      · exact Classical.byContradiction fun h => hNot (Or.inr (Or.inr fun h' => h h'.symm))
    simp only [Option.map_some]
    rcases hLt with h | h | h <;> simp [h]

/-- **The key hook covers a key writer.**  If the write `pre → mid` moved no
other thread's key, made no thread an unflagged remote core holds
budget-eligible (a key writer leaves the binding alone), and every remote core
is flagged or kept its slots (its queue may only shrink), then the hook's
post-state covers the step. -/
theorem markKeyChangeFor_covers {e : CoreId} {pre mid : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hPre : pre.getTcb? tid = some tcb)
    (hOthers : ∀ t, t ≠ tid → schedKeyView mid t = schedKeyView pre t)
    (hElig : ∀ c, c ≠ e → mid.scheduler.reschedulePendingOnCore c = false →
      ∀ t, mid.queuedOn c t = true → candidacyNotGained pre mid t)
    (hSlots : ∀ c, c ≠ e → mid.scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, mid.queuedOn c t = true → pre.queuedOn c t = true) ∧
        mid.scheduler.currentOnCore c = pre.scheduler.currentOnCore c)) :
    reschedulePendingCovers e pre
      (markKeyChangeFor mid tid (effectiveSchedParams pre tcb)) := by
  intro c hc
  cases hFl : mid.scheduler.reschedulePendingOnCore c
  case true => exact Or.inl (markKeyChangeFor_reschedulePendingOnCore_mono _ _ _ _ hFl)
  rcases hSlots c hc with hUp | ⟨hRq, hCur⟩
  · rw [hFl] at hUp; cases hUp
  by_cases hA : mid.queuedOn c tid = true ∧ schedKeyView mid tid ≠ schedKeyView pre tid
  · exact Or.inl (markKeyChangeFor_reschedulePendingOnCore_of_moved hPre hA.1 hA.2)
  by_cases hB : mid.scheduler.currentOnCore c = some tid ∧ ¬ schedKeyNotWeakened pre mid tid
  · exact Or.inl (markKeyChangeFor_reschedulePendingOnCore_of_weakened hPre hB.1 hB.2)
  right
  have hKey : ∀ t, mid.queuedOn c t = true → schedKeyView pre t = schedKeyView mid t := by
    intro t ht
    by_cases hEq : t = tid
    · subst hEq
      exact (Classical.byContradiction fun h => hA ⟨ht, fun h' => h h'.symm⟩)
    · exact (hOthers t hEq).symm
  refine ⟨fun t ht => ?_, ?_, fun t ht => ?_⟩
  · rw [markKeyChangeFor_queuedOn] at ht
    refine ⟨hRq t ht, (hKey t ht).trans (schedKeyView_markKeyChangeFor _ _ _ t).symm, ?_⟩
    unfold candidacyNotGained; rw [budgetEligibleView_markKeyChangeFor]; exact hElig c hc hFl t ht
  · simp only [markKeyChangeFor_currentOnCore]; exact hCur
  · simp only [markKeyChangeFor_currentOnCore] at ht
    intro kq hq
    rw [schedKeyView_markKeyChangeFor] at hq
    by_cases hEq : t = tid
    · subst hEq
      exact (Classical.byContradiction fun h => hB ⟨ht, fun h' => h (h' kq hq)⟩)
    · exact schedKeyNotWeakened_of_eq (hOthers t hEq).symm kq hq

/-! ### Per-thread flagging: the binding writers' hook -/

/-- Every core a key change on `tid` stales between `pre` and `post` is flagged
in `post`: a core whose queue holds `tid` when its key moved or it became
budget-eligible, and a core whose current slot holds it when its key weakened. -/
def keyChangeFlagged (pre post : SystemState) (tid : SeLe4n.ThreadId) : Prop :=
  ∀ c, ((post.queuedOn c tid = true ∧ (schedKeyView post tid ≠ schedKeyView pre tid ∨
        ¬ candidacyNotGained pre post tid)) ∨
      (post.scheduler.currentOnCore c = some tid ∧ ¬ schedKeyNotWeakened pre post tid)) →
    post.scheduler.reschedulePendingOnCore c = true

/-- **Coverage from per-thread flagging.**  A step whose every moved key is
flagged, and whose every remote core is flagged or kept its slots (its queue
may only shrink), covers. -/
theorem reschedulePendingCovers_of_keyChangeFlagged {e : CoreId} {pre post : SystemState}
    (hKeys : ∀ t, (schedKeyView post t = schedKeyView pre t ∧
      budgetEligibleView post t = budgetEligibleView pre t) ∨ keyChangeFlagged pre post t)
    (hSlots : ∀ c, c ≠ e → post.scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, post.queuedOn c t = true → pre.queuedOn c t = true) ∧
        post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c)) :
    reschedulePendingCovers e pre post := by
  intro c hc
  rcases hSlots c hc with hUp | ⟨hRq, hCur⟩
  · exact Or.inl hUp
  by_cases hF : post.scheduler.reschedulePendingOnCore c = true
  · exact Or.inl hF
  refine Or.inr ⟨fun t ht => ⟨hRq t ht, ?_, ?_⟩, hCur, fun t ht => ?_⟩
  · rcases hKeys t with h | h
    · exact h.1.symm
    · exact Classical.byContradiction fun hne =>
        hF (h c (Or.inl ⟨ht, Or.inl fun h' => hne h'.symm⟩))
  · rcases hKeys t with h | h
    · exact candidacyNotGained_of_eq h.2.symm
    · exact Classical.byContradiction fun hg => hF (h c (Or.inl ⟨ht, Or.inr hg⟩))
  · rcases hKeys t with h | h
    · exact schedKeyNotWeakened_of_eq h.1.symm
    · exact Classical.byContradiction fun hw => hF (h c (Or.inr ⟨ht, hw⟩))

/-- Flagging survives a later step that moves no slot, no key and no flag down. -/
theorem keyChangeFlagged_of_flagOnly {pre mid post : SystemState} {tid : SeLe4n.ThreadId}
    (h : keyChangeFlagged pre mid tid)
    (hRq : SystemState.RunCoresAgree post mid)
    (hCur : ∀ c, post.scheduler.currentOnCore c = mid.scheduler.currentOnCore c)
    (hKey : ∀ t, schedKeyView post t = schedKeyView mid t)
    (hElig : ∀ t, budgetEligibleView post t = budgetEligibleView mid t)
    (hMono : ∀ c, mid.scheduler.reschedulePendingOnCore c = true →
      post.scheduler.reschedulePendingOnCore c = true) :
    keyChangeFlagged pre post tid := by
  intro c hc
  apply hMono c
  apply h c
  have hW : schedKeyNotWeakened pre post tid ↔ schedKeyNotWeakened pre mid tid := by
    unfold schedKeyNotWeakened; rw [hKey]
  have hG : candidacyNotGained pre post tid ↔ candidacyNotGained pre mid tid := by
    unfold candidacyNotGained; rw [hElig]
  rw [hRq.queuedOn, hCur, hKey] at hc
  rcases hc with ⟨hq, hm | hg⟩ | ⟨hc1, hc2⟩
  · exact Or.inl ⟨hq, Or.inl hm⟩
  · exact Or.inl ⟨hq, Or.inr fun h' => hg (hG.mpr h')⟩
  · exact Or.inr ⟨hc1, fun hw => hc2 (hW.mpr hw)⟩

@[simp] theorem schedKeyView_markKeyChangeFrom (pre post : SystemState) (tid t : SeLe4n.ThreadId) :
    schedKeyView (markKeyChangeFrom pre post tid) t = schedKeyView post t :=
  markKeyChangeFrom_extract_frame (fun s => schedKeyView s t) pre post tid (fun _ _ => rfl)

@[simp] theorem budgetEligibleView_markKeyChangeFrom (pre post : SystemState)
    (tid t : SeLe4n.ThreadId) :
    budgetEligibleView (markKeyChangeFrom pre post tid) t = budgetEligibleView post t :=
  markKeyChangeFrom_extract_frame (fun s => budgetEligibleView s t) pre post tid (fun _ _ => rfl)

theorem markKeyChangeFrom_reschedulePendingOnCore_mono (pre post : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (h : post.scheduler.reschedulePendingOnCore c = true) :
    (markKeyChangeFrom pre post tid).scheduler.reschedulePendingOnCore c = true := by
  unfold markKeyChangeFrom
  split
  · exact markKeyChangeFor_reschedulePendingOnCore_mono _ _ _ _
      (markCandidacyGainFor_reschedulePendingOnCore_mono _ _ _ _ h)
  · simp [markReschedulePendingWhere_reschedulePendingOnCore, h]

/-- **The hook flags what it is called for**: every core the key change on
`tid` stales, read against `pre`. -/
theorem markKeyChangeFrom_flagged (pre mid : SystemState) (tid : SeLe4n.ThreadId) :
    keyChangeFlagged pre (markKeyChangeFrom pre mid tid) tid := by
  intro c hc
  rw [(SystemState.RunCoresAgree.of_objects (markKeyChangeFrom_objects pre mid tid)).queuedOn]
    at hc
  simp only [markKeyChangeFrom_currentOnCore, schedKeyView_markKeyChangeFrom] at hc
  have hW : schedKeyNotWeakened pre (markKeyChangeFrom pre mid tid) tid ↔
      schedKeyNotWeakened pre mid tid := by
    unfold schedKeyNotWeakened; simp only [schedKeyView_markKeyChangeFrom]
  have hG : candidacyNotGained pre (markKeyChangeFrom pre mid tid) tid ↔
      candidacyNotGained pre mid tid := by
    unfold candidacyNotGained; simp only [budgetEligibleView_markKeyChangeFrom]
  cases hT : pre.getTcb? tid with
  | some tcb =>
    let m' := markCandidacyGainFor mid tid (hasSufficientBudget pre tcb)
    have hEq : markKeyChangeFrom pre mid tid =
        markKeyChangeFor m' tid (effectiveSchedParams pre tcb) := by
      unfold markKeyChangeFrom; rw [hT]
    have hWm : schedKeyNotWeakened pre m' tid ↔ schedKeyNotWeakened pre mid tid := by
      unfold schedKeyNotWeakened; simp only [m', schedKeyView_markCandidacyGainFor]
    rw [hEq]
    rcases hc with ⟨hm, hne | hg⟩ | ⟨hcur, hw⟩
    · exact markKeyChangeFor_reschedulePendingOnCore_of_moved hT
        (by simpa [m'] using hm) (by simpa [m'] using hne)
    · exact markKeyChangeFor_reschedulePendingOnCore_mono _ _ _ _
        (markCandidacyGainFor_reschedulePendingOnCore_of_gained hT hm
          (fun h' => hg (hG.mpr h')))
    · exact markKeyChangeFor_reschedulePendingOnCore_of_weakened hT
        (by simpa [m'] using hcur) (fun h' => hw (hW.mpr (hWm.mp h')))
  | none =>
    have hEq : markKeyChangeFrom pre mid tid = markReschedulePendingWhere mid
        (fun c => mid.queuedOn c tid ||
          mid.scheduler.currentOnCore c == some tid) allCores := by
      unfold markKeyChangeFrom; rw [hT]
    rw [hEq, markReschedulePendingWhere_reschedulePendingOnCore]
    rcases hc with ⟨hm, -⟩ | ⟨hcur, -⟩
    · simp [hm]
    · simp [hcur]

/-- **The pre-state hook covers a binding writer.**  If the write `pre → mid`
moved no other thread's key or budget eligibility, and every remote core is
flagged or kept its slots (its queue may only shrink), then the hook's
post-state covers the step: whatever the write did to `tid` itself (its key,
its binding, its eligibility) the hook flags. -/
theorem markKeyChangeFrom_covers {e : CoreId} {pre mid : SystemState} {tid : SeLe4n.ThreadId}
    (hOthers : ∀ t, t ≠ tid → schedKeyView mid t = schedKeyView pre t ∧
      budgetEligibleView mid t = budgetEligibleView pre t)
    (hSlots : ∀ c, c ≠ e → mid.scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, mid.queuedOn c t = true → pre.queuedOn c t = true) ∧
        mid.scheduler.currentOnCore c = pre.scheduler.currentOnCore c)) :
    reschedulePendingCovers e pre (markKeyChangeFrom pre mid tid) := by
  refine reschedulePendingCovers_of_keyChangeFlagged (fun t => ?_) (fun c hc => ?_)
  · by_cases ht : t = tid
    · subst ht; exact Or.inr (markKeyChangeFrom_flagged pre mid t)
    · left
      simp only [schedKeyView_markKeyChangeFrom, budgetEligibleView_markKeyChangeFrom]
      exact hOthers t ht
  · rcases hSlots c hc with hUp | ⟨hRq, hCur⟩
    · exact Or.inl (markKeyChangeFrom_reschedulePendingOnCore_mono pre mid tid c hUp)
    · refine Or.inr ⟨fun t ht => hRq t ?_, ?_⟩
      · rwa [(SystemState.RunCoresAgree.of_objects (markKeyChangeFrom_objects pre mid tid)).queuedOn]
          at ht
      · rw [markKeyChangeFrom_currentOnCore]; exact hCur

/-- The hook pair a writer that read `tid`'s TCB before writing spells out (the
key hook over the candidacy hook) is the pre-state hook. -/
theorem markKeyChangeFor_markCandidacyGainFor_eq {pre mid : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hPre : pre.getTcb? tid = some tcb) :
    markKeyChangeFor (markCandidacyGainFor mid tid (hasSufficientBudget pre tcb)) tid
      (effectiveSchedParams pre tcb) = markKeyChangeFrom pre mid tid := by
  unfold markKeyChangeFrom; rw [hPre]

/-! ### The key inputs as an object-store relation

The effective key reads a TCB's four key fields and a scheduling context's
deadline, and budget eligibility reads the binding and the context's budget
sign; nothing else in the object store is read by either.  `keyInputsOf`
projects one object slot onto exactly that, so "no chooser input moved" is a
property of the object store that composes by `.trans` and that a single store
lemma establishes for every write whose slot keeps its projection. -/

/-- What one object slot contributes to any thread's effective key and budget
eligibility, and the core whose run queue a TCB's links place it on (WS-ZA
ZA4.5: the coverage reads queue membership off the TCB links, so the core is an
input too).  A scheduling context contributes its deadline (the key) and
whether budget is left (`hasSufficientBudget`). -/
def keyInputsOf : Option KernelObject →
    Option ((SeLe4n.Priority × SeLe4n.Deadline × SchedContextBinding ×
      Option SeLe4n.Priority × SeLe4n.DomainId × Nat) ⊕ (SeLe4n.Deadline × Bool))
  | some (.tcb t) =>
      some (.inl (t.priority, t.deadline, t.schedContextBinding, t.pipBoost, t.domain,
        t.runCoreCode))
  | some (.schedContext sc) => some (.inr (sc.deadline, sc.budgetRemaining.isPositive))
  | _ => none

/-- No object slot's key inputs moved from `pre` to `post`. -/
def keyInputsEq (pre post : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, keyInputsOf post.objects[oid]? = keyInputsOf pre.objects[oid]?

theorem keyInputsEq_refl (st : SystemState) : keyInputsEq st st := fun _ => rfl

theorem keyInputsEq_trans {a b d : SystemState} (h₁ : keyInputsEq a b) (h₂ : keyInputsEq b d) :
    keyInputsEq a d := fun oid => (h₂ oid).trans (h₁ oid)

theorem keyInputsEq_of_objects_eq {pre post : SystemState} (h : post.objects = pre.objects) :
    keyInputsEq pre post := fun oid => by rw [h]

/-- A store whose value keeps its slot's key inputs moves no key input. -/
theorem keyInputsEq_storeObject {st st' : SystemState} {oid : SeLe4n.ObjId}
    {obj : KernelObject} (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hKey : keyInputsOf (some obj) = keyInputsOf st.objects[oid]?) :
    keyInputsEq st st' := by
  intro k
  by_cases hEq : k = oid
  · subst hEq; rw [storeObject_objects_eq st st' k obj hObjInv hStore]; exact hKey
  · rw [storeObject_objects_ne st st' oid k obj hEq hObjInv hStore]

/-- The scheduler record is no key input. -/
theorem keyInputsEq_with_scheduler (st : SystemState) (s : SchedulerState) :
    keyInputsEq st { st with scheduler := s } := fun _ => rfl

/-- WS-ZA ZA4.5: two slots that agree off the run-queue links and name the same
run-queue core carry the same key inputs. -/
theorem keyInputsOf_eq_of_offRunLinks {a b : Option KernelObject}
    (hw : a.map KernelObject.withoutRunLinks = b.map KernelObject.withoutRunLinks)
    (hr : ∀ t t', a = some (.tcb t) → b = some (.tcb t') → t.runCoreCode = t'.runCoreCode) :
    keyInputsOf a = keyInputsOf b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some _ => simp at hw
  | some o => cases b with
    | none => simp at hw
    | some o' =>
      simp only [Option.map_some, Option.some.injEq] at hw
      by_cases ht : ∃ t', o' = .tcb t'
      · obtain ⟨t', rfl⟩ := ht
        obtain ⟨t, rfl, e⟩ := KernelObject.withoutRunLinks_eq_tcb hw
        have hc := hr t t' rfl rfl
        simp only [keyInputsOf, hc, TCB.proj_eq_of_withoutRunLinks_eq TCB.priority e,
          TCB.proj_eq_of_withoutRunLinks_eq TCB.deadline e,
          TCB.proj_eq_of_withoutRunLinks_eq TCB.schedContextBinding e,
          TCB.proj_eq_of_withoutRunLinks_eq TCB.pipBoost e,
          TCB.proj_eq_of_withoutRunLinks_eq TCB.domain e]
      · have hNot : ∀ t', o' ≠ .tcb t' := fun t' h => ht ⟨t', h⟩
        rw [KernelObject.withoutRunLinks_eq_self_of_not_tcb hNot] at hw
        have hNotO : ∀ t, o ≠ .tcb t := fun t h => by
          subst h; exact hNot _ (by simpa using hw.symm)
        rw [KernelObject.withoutRunLinks_eq_self_of_not_tcb hNotO] at hw
        rw [hw]

/-- The thread whose TCB an object slot would hold. -/
theorem runCoreCode_eq_of_slot {pre post : SystemState} {oid : SeLe4n.ObjId}
    (hc : (post.getTcb? (SeLe4n.ThreadId.ofNat oid.toNat)).map TCB.runCoreCode =
      (pre.getTcb? (SeLe4n.ThreadId.ofNat oid.toNat)).map TCB.runCoreCode) :
    ∀ t t', post.objects[oid]? = some (.tcb t) → pre.objects[oid]? = some (.tcb t') →
      t.runCoreCode = t'.runCoreCode := fun t t' ha hb => by
  rw [(SystemState.getTcb?_eq_some_iff post (SeLe4n.ThreadId.ofNat oid.toNat) t).mpr ha,
    (SystemState.getTcb?_eq_some_iff pre (SeLe4n.ThreadId.ofNat oid.toNat) t').mpr hb] at hc
  simpa using hc

/-- WS-ZA ZA4.5: the run-queue links other than the core are no key input. -/
theorem keyInputsEq_of_objectsAgreeOffRunLinks {pre post : SystemState}
    (h : post.objectsAgreeOffRunLinks pre) (hRun : SystemState.RunCoresAgree post pre) :
    keyInputsEq pre post := fun oid =>
  keyInputsOf_eq_of_offRunLinks (h oid) (runCoreCode_eq_of_slot (hRun _))

/-- WS-ZA ZA4.6: the reply-waiter links are no key input either. -/
theorem keyInputsEq_of_objectsAgreeOffReplyLinks {pre post : SystemState}
    (h : post.objectsAgreeOffReplyLinks pre) : keyInputsEq pre post := fun oid => by
  have hv : ∀ x : Option KernelObject,
      keyInputsOf (x.map KernelObject.withoutReplyLinks) = keyInputsOf x := by
    intro x; rcases x with _ | o
    · rfl
    · cases o <;> rfl
  rw [← hv post.objects[oid]?, h oid, hv]

/-- WS-ZA ZA6.3: the release-queue links are no key input either. -/
theorem keyInputsEq_of_objectsAgreeOffReleaseLinks {pre post : SystemState}
    (h : post.objectsAgreeOffReleaseLinks pre) : keyInputsEq pre post := fun oid => by
  have hv : ∀ x : Option KernelObject,
      keyInputsOf (x.map KernelObject.withoutRelease) = keyInputsOf x := by
    intro x; rcases x with _ | o
    · rfl
    · cases o <;> rfl
  rw [← hv post.objects[oid]?, h oid, hv]

/-- WS-ZA ZA5.11: the taint words are no key input either. -/
theorem keyInputsEq_of_objectsAgreeOffTaint {pre post : SystemState}
    (h : pre.objectsAgreeOffTaint post) : keyInputsEq pre post := fun oid => by
  have hv : ∀ x : Option KernelObject,
      keyInputsOf (x.map KernelObject.eraseTaint) = keyInputsOf x := by
    intro x; rcases x with _ | o
    · rfl
    · cases o <;> rfl
  rw [← hv post.objects[oid]?, h oid, hv]

/-- Equal key inputs place every thread on the same run-queue core. -/
theorem keyInputsEq.runCoresAgree {pre post : SystemState} (h : keyInputsEq pre post) :
    SystemState.RunCoresAgree post pre := fun y => by
  have hk := h y.toObjId
  unfold SystemState.getTcb?
  revert hk
  generalize post.objects[y.toObjId]? = a
  generalize pre.objects[y.toObjId]? = b
  intro hk
  cases a with
  | none => cases b with
    | none => rfl
    | some o => cases o <;> simp_all [keyInputsOf]
  | some o => cases b with
    | none => cases o <;> simp_all [keyInputsOf]
    | some o' => cases o <;> cases o' <;> simp_all [keyInputsOf]

/-- A TCB's five key fields. -/
def tcbKeyFields (t : TCB) :
    SeLe4n.Priority × SeLe4n.Deadline × SchedContextBinding × Option SeLe4n.Priority ×
      SeLe4n.DomainId :=
  (t.priority, t.deadline, t.schedContextBinding, t.pipBoost, t.domain)

/-- One slot's key inputs fix a TCB's key fields there. -/
theorem getTcb?_keyFields_of_keyInputsOf {pre post : SystemState} {t : SeLe4n.ThreadId}
    (hk : keyInputsOf post.objects[t.toObjId]? = keyInputsOf pre.objects[t.toObjId]?) :
    (post.getTcb? t).map tcbKeyFields = (pre.getTcb? t).map tcbKeyFields := by
  unfold SystemState.getTcb?
  revert hk
  generalize post.objects[t.toObjId]? = a
  generalize pre.objects[t.toObjId]? = b
  intro hk
  cases a with
  | none => cases b with
    | none => rfl
    | some o => cases o <;> simp_all [keyInputsOf]
  | some o => cases b with
    | none => cases o <;> simp_all [keyInputsOf]
    | some o' => cases o <;> cases o' <;> simp_all [keyInputsOf, tcbKeyFields]

theorem getTcb?_keyFields_of_keyInputsEq {pre post : SystemState} (h : keyInputsEq pre post)
    (t : SeLe4n.ThreadId) :
    (post.getTcb? t).map tcbKeyFields = (pre.getTcb? t).map tcbKeyFields :=
  getTcb?_keyFields_of_keyInputsOf (h t.toObjId)

/-- One slot's key inputs fix a scheduling context's deadline there. -/
theorem getSchedContext?_deadline_of_keyInputsOf {pre post : SystemState}
    {sc : SeLe4n.SchedContextId}
    (hk : keyInputsOf post.objects[sc.toObjId]? = keyInputsOf pre.objects[sc.toObjId]?) :
    (post.getSchedContext? sc).map (·.deadline) = (pre.getSchedContext? sc).map (·.deadline) := by
  unfold SystemState.getSchedContext?
  revert hk
  generalize post.objects[sc.toObjId]? = a
  generalize pre.objects[sc.toObjId]? = b
  intro hk
  cases a with
  | none => cases b with
    | none => rfl
    | some o => cases o <;> simp_all [keyInputsOf]
  | some o => cases b with
    | none => cases o <;> simp_all [keyInputsOf]
    | some o' => cases o <;> cases o' <;> simp_all [keyInputsOf]

theorem getSchedContext?_deadline_of_keyInputsEq {pre post : SystemState}
    (h : keyInputsEq pre post) (sc : SeLe4n.SchedContextId) :
    (post.getSchedContext? sc).map (·.deadline) = (pre.getSchedContext? sc).map (·.deadline) :=
  getSchedContext?_deadline_of_keyInputsOf (h sc.toObjId)

/-- One slot's key inputs fix a scheduling context's budget sign there. -/
theorem getSchedContext?_budget_of_keyInputsOf {pre post : SystemState}
    {sc : SeLe4n.SchedContextId}
    (hk : keyInputsOf post.objects[sc.toObjId]? = keyInputsOf pre.objects[sc.toObjId]?) :
    (post.getSchedContext? sc).map (·.budgetRemaining.isPositive) =
      (pre.getSchedContext? sc).map (·.budgetRemaining.isPositive) := by
  unfold SystemState.getSchedContext?
  revert hk
  generalize post.objects[sc.toObjId]? = a
  generalize pre.objects[sc.toObjId]? = b
  intro hk
  cases a with
  | none => cases b with
    | none => rfl
    | some o => cases o <;> simp_all [keyInputsOf]
  | some o => cases b with
    | none => cases o <;> simp_all [keyInputsOf]
    | some o' => cases o <;> cases o' <;> simp_all [keyInputsOf]

theorem getSchedContext?_budget_of_keyInputsEq {pre post : SystemState}
    (h : keyInputsEq pre post) (sc : SeLe4n.SchedContextId) :
    (post.getSchedContext? sc).map (·.budgetRemaining.isPositive) =
      (pre.getSchedContext? sc).map (·.budgetRemaining.isPositive) :=
  getSchedContext?_budget_of_keyInputsOf (h sc.toObjId)

/-- Budget eligibility over a slot pair that fixes the key fields, given the
contexts' budget signs. -/
theorem budgetEligibleView_eq_of_keyFields {pre post : SystemState} {t : SeLe4n.ThreadId}
    (hT : (post.getTcb? t).map tcbKeyFields = (pre.getTcb? t).map tcbKeyFields)
    (hSc : ∀ sc, (post.getSchedContext? sc).map (·.budgetRemaining.isPositive) =
      (pre.getSchedContext? sc).map (·.budgetRemaining.isPositive)) :
    budgetEligibleView post t = budgetEligibleView pre t := by
  unfold budgetEligibleView
  cases hq : post.getTcb? t <;> cases hp : pre.getTcb? t <;> simp only [hq, hp] at hT ⊢
  · rfl
  · simp at hT
  · simp at hT
  · simp only [Option.map_some, Option.some.injEq, tcbKeyFields, Prod.mk.injEq] at hT ⊢
    exact hasSufficientBudget_congr hSc hT.2.2.1

/-- Equal key inputs give equal budget eligibility for every thread. -/
theorem budgetEligibleView_eq_of_keyInputsEq {pre post : SystemState} (h : keyInputsEq pre post)
    (t : SeLe4n.ThreadId) : budgetEligibleView post t = budgetEligibleView pre t :=
  budgetEligibleView_eq_of_keyFields (getTcb?_keyFields_of_keyInputsEq h t)
    (getSchedContext?_budget_of_keyInputsEq h)

/-- The effective key reads the key fields and the contexts' deadlines alone. -/
theorem resolveEffectivePrioDeadline_congr_deadline {st st' : SystemState} {a b : TCB}
    (hSc : ∀ sc, (st'.getSchedContext? sc).map (·.deadline) =
      (st.getSchedContext? sc).map (·.deadline))
    (hK : tcbKeyFields b = tcbKeyFields a) :
    resolveEffectivePrioDeadline st' b = resolveEffectivePrioDeadline st a := by
  simp only [tcbKeyFields, Prod.mk.injEq] at hK
  obtain ⟨hP, hD, hB, hPip, -⟩ := hK
  unfold resolveEffectivePrioDeadline
  rw [hP, hD, hB, hPip]
  cases a.schedContextBinding with
  | unbound => rfl
  | bound sc =>
    have := hSc sc
    cases hq : st'.getSchedContext? sc <;> cases hp : st.getSchedContext? sc <;> simp_all
  | donated sc o =>
    have := hSc sc
    cases hq : st'.getSchedContext? sc <;> cases hp : st.getSchedContext? sc <;> simp_all

/-- The full key reads the key fields and the contexts' deadlines alone. -/
theorem effectiveSchedParams_congr_deadline {st st' : SystemState} {a b : TCB}
    (hSc : ∀ sc, (st'.getSchedContext? sc).map (·.deadline) =
      (st.getSchedContext? sc).map (·.deadline))
    (hK : tcbKeyFields b = tcbKeyFields a) :
    effectiveSchedParams st' b = effectiveSchedParams st a := by
  have hDom : b.domain = a.domain := by
    simp only [tcbKeyFields, Prod.mk.injEq] at hK; exact hK.2.2.2.2
  exact effectiveSchedParams_eq_of (resolveEffectivePrioDeadline_congr_deadline hSc hK) hDom

/-- Equal key inputs give equal keys for every thread. -/
theorem schedKeyView_eq_of_keyInputsEq {pre post : SystemState} (h : keyInputsEq pre post)
    (t : SeLe4n.ThreadId) : schedKeyView post t = schedKeyView pre t := by
  have hT := getTcb?_keyFields_of_keyInputsEq h t
  unfold schedKeyView
  cases hq : post.getTcb? t <;> cases hp : pre.getTcb? t <;> simp only [hq, hp] at hT ⊢
  · rfl
  · simp at hT
  · simp at hT
  · simp only [Option.map_some, Option.some.injEq] at hT ⊢
    rw [effectiveSchedParams_congr_deadline
      (getSchedContext?_deadline_of_keyInputsEq h) hT]

/-- Equal key inputs followed by a run-queue link rewrite move no thread's key. -/
theorem schedKeyView_of_keyInputsEq_offRunLinks {pre mid post : SystemState}
    (h₁ : keyInputsEq pre mid) (h₂ : post.objectsAgreeOffRunLinks mid) (t : SeLe4n.ThreadId) :
    schedKeyView post t = schedKeyView pre t :=
  (schedKeyView_of_objectsAgreeOffRunLinks h₂ t).trans (schedKeyView_eq_of_keyInputsEq h₁ t)

/-- Equal key inputs followed by a run-queue link rewrite move no thread's budget
eligibility. -/
theorem budgetEligibleView_of_keyInputsEq_offRunLinks {pre mid post : SystemState}
    (h₁ : keyInputsEq pre mid) (h₂ : post.objectsAgreeOffRunLinks mid) (t : SeLe4n.ThreadId) :
    budgetEligibleView post t = budgetEligibleView pre t :=
  (budgetEligibleView_of_objectsAgreeOffRunLinks h₂ t).trans
    (budgetEligibleView_eq_of_keyInputsEq h₁ t)

/-- **No key input moved but `tid`'s own TCB's**, and `tid`'s slot holds no
scheduling context on either side, so no other thread's key can read it. -/
def keyInputsEqExcept (tid : SeLe4n.ThreadId) (pre post : SystemState) : Prop :=
  (∀ oid, oid ≠ tid.toObjId →
    keyInputsOf post.objects[oid]? = keyInputsOf pre.objects[oid]?) ∧
  (∀ sc, pre.objects[tid.toObjId]? ≠ some (.schedContext sc)) ∧
  (∀ sc, post.objects[tid.toObjId]? ≠ some (.schedContext sc))

theorem keyInputsEqExcept.trans {tid : SeLe4n.ThreadId} {a b d : SystemState}
    (h₁ : keyInputsEqExcept tid a b) (h₂ : keyInputsEqExcept tid b d) :
    keyInputsEqExcept tid a d :=
  ⟨fun oid h => (h₂.1 oid h).trans (h₁.1 oid h), h₁.2.1, h₂.2.2⟩

theorem keyInputsEqExcept.trans_keyInputsEq {tid : SeLe4n.ThreadId} {a b d : SystemState}
    (h₁ : keyInputsEqExcept tid a b) (h₂ : keyInputsEq b d) : keyInputsEqExcept tid a d := by
  refine ⟨fun oid h => (h₂ oid).trans (h₁.1 oid h), h₁.2.1, fun sc hd => ?_⟩
  have hk := h₂ tid.toObjId
  rw [hd] at hk
  cases hb : b.objects[tid.toObjId]? with
  | none => rw [hb] at hk; cases hk
  | some o =>
    rw [hb] at hk
    cases o <;> simp [keyInputsOf] at hk
    exact h₁.2.2 _ hb

/-- A run-queue link rewrite that moves no core but `tid`'s keeps every key input
but `tid`'s. -/
theorem keyInputsEqExcept.trans_offRunLinks {tid : SeLe4n.ThreadId} {a b d : SystemState}
    (h₁ : keyInputsEqExcept tid a b) (h₂ : d.objectsAgreeOffRunLinks b)
    (hRun : ∀ y, y ≠ tid → (d.getTcb? y).map TCB.runCoreCode = (b.getTcb? y).map TCB.runCoreCode) :
    keyInputsEqExcept tid a d := by
  refine ⟨fun oid h => ?_, h₁.2.1, fun sc hd => ?_⟩
  · refine (keyInputsOf_eq_of_offRunLinks (h₂ oid) (runCoreCode_eq_of_slot (hRun _ ?_))).trans
      (h₁.1 oid h)
    intro e; exact h (by rw [← e]; rfl)
  · have hw := h₂ tid.toObjId
    rw [hd] at hw
    cases hb : b.objects[tid.toObjId]? with
    | none => rw [hb] at hw; cases hw
    | some o =>
      rw [hb] at hw
      simp only [Option.map_some, Option.some.injEq] at hw
      cases o with
      | tcb t => simp [KernelObject.withoutRunLinks] at hw
      | schedContext sc' =>
        exact h₁.2.2 sc' hb
      | _ => simp [KernelObject.withoutRunLinks] at hw

theorem keyInputsEq.trans_keyInputsEqExcept {tid : SeLe4n.ThreadId} {a b d : SystemState}
    (h₁ : keyInputsEq a b) (h₂ : keyInputsEqExcept tid b d) : keyInputsEqExcept tid a d := by
  refine ⟨fun oid h => (h₂.1 oid h).trans (h₁ oid), fun sc ha => ?_, h₂.2.2⟩
  have hk := h₁ tid.toObjId
  rw [ha] at hk
  cases hb : b.objects[tid.toObjId]? with
  | none => rw [hb] at hk; cases hk
  | some o =>
    rw [hb] at hk
    cases o <;> simp [keyInputsOf] at hk
    exact h₂.2.1 _ hb

/-- No scheduling context lives at `tid`'s slot on either side of a
`keyInputsEqExcept tid` step, so every context's inputs are framed. -/
theorem keyInputsEqExcept.schedContext_frame {tid : SeLe4n.ThreadId} {pre post : SystemState}
    (h : keyInputsEqExcept tid pre post) (sc : SeLe4n.SchedContextId) :
    (sc.toObjId = tid.toObjId → post.getSchedContext? sc = none ∧ pre.getSchedContext? sc = none) ∧
    (sc.toObjId ≠ tid.toObjId →
      keyInputsOf post.objects[sc.toObjId]? = keyInputsOf pre.objects[sc.toObjId]?) := by
  refine ⟨fun hs => ⟨?_, ?_⟩, fun hs => h.1 _ hs⟩
  · unfold SystemState.getSchedContext?; rw [hs]
    split
    · rename_i x hx; exact absurd hx (h.2.2 x)
    · rfl
  · unfold SystemState.getSchedContext?; rw [hs]
    split
    · rename_i x hx; exact absurd hx (h.2.1 x)
    · rfl

/-- Every other thread keeps its budget eligibility. -/
theorem budgetEligibleView_eq_of_keyInputsEqExcept {tid : SeLe4n.ThreadId}
    {pre post : SystemState} (h : keyInputsEqExcept tid pre post) {t : SeLe4n.ThreadId}
    (ht : t ≠ tid) : budgetEligibleView post t = budgetEligibleView pre t := by
  have hNe : t.toObjId ≠ tid.toObjId := fun e => ht (SeLe4n.ThreadId.toObjId_injective _ _ e)
  refine budgetEligibleView_eq_of_keyFields (getTcb?_keyFields_of_keyInputsOf (h.1 _ hNe))
    fun sc => ?_
  by_cases hs : sc.toObjId = tid.toObjId
  · obtain ⟨hq, hp⟩ := (h.schedContext_frame sc).1 hs
    rw [hq, hp]
  · exact getSchedContext?_budget_of_keyInputsOf ((h.schedContext_frame sc).2 hs)

/-- `tid` itself keeps its budget eligibility when its binding did not move. -/
theorem budgetEligibleView_self_of_keyInputsEqExcept {tid : SeLe4n.ThreadId}
    {pre post : SystemState} (h : keyInputsEqExcept tid pre post)
    (hB : (post.getTcb? tid).map TCB.schedContextBinding =
      (pre.getTcb? tid).map TCB.schedContextBinding) :
    budgetEligibleView post tid = budgetEligibleView pre tid := by
  have hSc : ∀ sc, (post.getSchedContext? sc).map (·.budgetRemaining.isPositive) =
      (pre.getSchedContext? sc).map (·.budgetRemaining.isPositive) := by
    intro sc
    by_cases hs : sc.toObjId = tid.toObjId
    · obtain ⟨hq, hp⟩ := (h.schedContext_frame sc).1 hs
      rw [hq, hp]
    · exact getSchedContext?_budget_of_keyInputsOf ((h.schedContext_frame sc).2 hs)
  unfold budgetEligibleView
  cases hq : post.getTcb? tid <;> cases hp : pre.getTcb? tid <;> simp only [hq, hp] at hB ⊢
  · rfl
  · simp at hB
  · simp at hB
  · simp only [Option.map_some, Option.some.injEq] at hB ⊢
    exact hasSufficientBudget_congr hSc hB

/-- No thread's scheduling-context binding moved from `pre` to `post`. -/
def bindingsAgree (post pre : SystemState) : Prop :=
  ∀ t, (post.getTcb? t).map TCB.schedContextBinding = (pre.getTcb? t).map TCB.schedContextBinding

theorem bindingsAgree.refl (st : SystemState) : bindingsAgree st st := fun _ => rfl

theorem bindingsAgree.trans {a b d : SystemState} (h₁ : bindingsAgree d b)
    (h₂ : bindingsAgree b a) : bindingsAgree d a := fun t => (h₁ t).trans (h₂ t)

theorem bindingsAgree.of_objects_eq {pre post : SystemState} (h : post.objects = pre.objects) :
    bindingsAgree post pre := fun t => by unfold SystemState.getTcb?; rw [h]

/-- WS-ZA ZA4.5: the run-queue links are no binding. -/
theorem bindingsAgree.of_objectsAgreeOffRunLinks {pre post : SystemState}
    (h : post.objectsAgreeOffRunLinks pre) : bindingsAgree post pre := fun t =>
  TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.schedContextBinding (h.getTcb? t)

/-- A TCB update keeping the binding moves no binding. -/
theorem bindingsAgree.updateTcb {st : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ t, (f t).schedContextBinding = t.schedContextBinding) :
    bindingsAgree (st.updateTcb tid f) st := fun y => by
  by_cases h : tid.toObjId = y.toObjId
  · cases SeLe4n.ThreadId.toObjId_injective tid y h
    rw [SystemState.updateTcb_getTcb?_self st tid f hInv]
    cases st.getTcb? tid with
    | none => rfl
    | some t => simp only [Option.map_some, hf]
  · rw [SystemState.updateTcb_getTcb?_ne st tid f hInv y h]

/-- A scheduling-context update moves no binding. -/
theorem bindingsAgree.updateSchedContext {st : SystemState} {scId : SeLe4n.SchedContextId}
    {f : SchedContext → SchedContext} (hInv : st.objects.invExt) :
    bindingsAgree (st.updateSchedContext scId f) st := fun y => by
  rw [SystemState.updateSchedContext_getTcb? st scId f hInv y]

/-- `tid` itself keeps its budget eligibility when no binding moved. -/
theorem budgetEligibleView_self_of_bindingsAgree {tid : SeLe4n.ThreadId}
    {pre post : SystemState} (h : keyInputsEqExcept tid pre post) (hB : bindingsAgree post pre) :
    budgetEligibleView post tid = budgetEligibleView pre tid :=
  budgetEligibleView_self_of_keyInputsEqExcept h (hB tid)

/-- Every other thread keeps its key. -/
theorem schedKeyView_eq_of_keyInputsEqExcept {tid : SeLe4n.ThreadId} {pre post : SystemState}
    (h : keyInputsEqExcept tid pre post) {t : SeLe4n.ThreadId} (ht : t ≠ tid) :
    schedKeyView post t = schedKeyView pre t := by
  have hNe : t.toObjId ≠ tid.toObjId := fun e => ht (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hT := getTcb?_keyFields_of_keyInputsOf (h.1 _ hNe)
  have hSc : ∀ sc, (post.getSchedContext? sc).map (·.deadline) =
      (pre.getSchedContext? sc).map (·.deadline) := by
    intro sc
    by_cases hs : sc.toObjId = tid.toObjId
    · have hq : post.getSchedContext? sc = none := by
        unfold SystemState.getSchedContext?; rw [hs]
        split
        · rename_i x hx; exact absurd hx (h.2.2 x)
        · rfl
      have hp : pre.getSchedContext? sc = none := by
        unfold SystemState.getSchedContext?; rw [hs]
        split
        · rename_i x hx; exact absurd hx (h.2.1 x)
        · rfl
      rw [hq, hp]
    · exact getSchedContext?_deadline_of_keyInputsOf (h.1 _ hs)
  unfold schedKeyView
  cases hq : post.getTcb? t <;> cases hp : pre.getTcb? t <;> simp only [hq, hp] at hT ⊢
  · rfl
  · simp at hT
  · simp at hT
  · simp only [Option.map_some, Option.some.injEq] at hT ⊢
    rw [effectiveSchedParams_congr_deadline hSc hT]

/-- A TCB update at `tid` moves no key input but `tid`'s. -/
theorem keyInputsEqExcept_updateTcb {st : SystemState} {tid : SeLe4n.ThreadId}
    {f : TCB → TCB} (hInv : st.objects.invExt) (hT : (st.getTcb? tid).isSome) :
    keyInputsEqExcept tid st (st.updateTcb tid f) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hT
  have hO : st.objects[tid.toObjId]? = some (.tcb t) := by
    unfold SystemState.getTcb? at ht; split at ht <;> simp_all
  unfold SystemState.updateTcb keyInputsEqExcept
  rw [SystemState.getTcbWitnessed?_eq_some ht]
  refine ⟨?_, ?_, ?_⟩
  · intro oid h
    show keyInputsOf (st.rewriteObject _ _ _).objects[oid]? = _
    rw [SystemState.rewriteObject_objects_ne st _ oid _ _ (Ne.symm h) hInv]
  · intro sc hs; rw [hO] at hs; cases hs
  · intro sc hs
    change (st.rewriteObject _ _ _).objects[tid.toObjId]? = _ at hs
    rw [SystemState.rewriteObject_objects_self st _ _ _ hInv] at hs; cases hs

/-- An in-place rewrite that keeps its slot's key inputs moves none. -/
theorem keyInputsEq_rewriteObject {st : SystemState} {id : SeLe4n.ObjId} {new : KernelObject}
    (h : st.rewriteAdmissible id new) (hInv : st.objects.invExt)
    (hKey : keyInputsOf (some new) = keyInputsOf st.objects[id]?) :
    keyInputsEq st (st.rewriteObject id new h) := by
  intro k
  by_cases hEq : id = k
  · subst hEq; rw [SystemState.rewriteObject_objects_self st id new h hInv]; exact hKey
  · rw [SystemState.rewriteObject_objects_ne st id k new h hEq hInv]

/-- A TCB update that keeps every key field moves no key input. -/
theorem keyInputsEq_updateTcb {st : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hF : ∀ t, tcbKeyFields (f t) = tcbKeyFields t)
    (hR : ∀ t, (f t).runCoreCode = t.runCoreCode := by intro _; rfl) :
    keyInputsEq st (st.updateTcb tid f) := by
  cases hT : st.getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact keyInputsEq_refl st
  | some t =>
    unfold SystemState.updateTcb
    rw [SystemState.getTcbWitnessed?_eq_some hT]
    apply keyInputsEq_rewriteObject _ hInv
    have hO : st.objects[tid.toObjId]? = some (.tcb t) := by
      unfold SystemState.getTcb? at hT; split at hT <;> simp_all
    rw [hO]
    have := hF t
    simp only [tcbKeyFields, Prod.mk.injEq] at this
    simp only [keyInputsOf, this, hR t]

/-! ### Steps that cover by frame -/

/-! ### Steps that keep every TCB a TCB -/

/-- **Every TCB of `pre` is a TCB of `post`**: what every step but the final
retire does to the store, the source of `residentTcbKeptOffCore`. -/
def tcbsKept (pre post : SystemState) : Prop :=
  ∀ t, (pre.getTcb? t).isSome → (post.getTcb? t).isSome

namespace tcbsKept

theorem refl (st : SystemState) : tcbsKept st st := fun _ h => h

theorem trans {a b d : SystemState} (h₁ : tcbsKept a b) (h₂ : tcbsKept b d) : tcbsKept a d :=
  fun t h => h₂ t (h₁ t h)

theorem of_objects_eq {pre post : SystemState} (h : post.objects = pre.objects) :
    tcbsKept pre post := fun t ht => by unfold SystemState.getTcb? at ht ⊢; rw [h]; exact ht

theorem of_getTcb? {pre post : SystemState} (h : ∀ t, post.getTcb? t = pre.getTcb? t) :
    tcbsKept pre post := fun t ht => by rw [h t]; exact ht

/-- Equal key views: the view is `none` exactly when no TCB is stored. -/
theorem of_view {pre post : SystemState} {t : SeLe4n.ThreadId}
    (h : schedKeyView post t = schedKeyView pre t) (hT : (pre.getTcb? t).isSome) :
    (post.getTcb? t).isSome := by
  have := congrArg Option.isSome h
  simp only [schedKeyView, Option.isSome_map] at this
  rw [this]; exact hT

theorem of_views {pre post : SystemState} (h : ∀ t, schedKeyView post t = schedKeyView pre t) :
    tcbsKept pre post := fun t => of_view (h t)

theorem of_views_except {pre post : SystemState} (tid : SeLe4n.ThreadId)
    (h : ∀ t, t ≠ tid → schedKeyView post t = schedKeyView pre t)
    (hTid : (post.getTcb? tid).isSome) : tcbsKept pre post := fun t hT => by
  by_cases ht : t = tid
  · subst ht; exact hTid
  · exact of_view (h t ht) hT

theorem of_keyInputsEq {pre post : SystemState} (h : keyInputsEq pre post) : tcbsKept pre post :=
  of_views (schedKeyView_eq_of_keyInputsEq h)

theorem of_keysExcept {tid : SeLe4n.ThreadId} {pre post : SystemState}
    (h : keyInputsEqExcept tid pre post) (hTid : (post.getTcb? tid).isSome) : tcbsKept pre post :=
  of_views_except tid (fun _ ht => schedKeyView_eq_of_keyInputsEqExcept h ht) hTid

theorem of_runLinks {pre post : SystemState} (h : post.objectsAgreeOffRunLinks pre) :
    tcbsKept pre post := of_views (schedKeyView_of_objectsAgreeOffRunLinks h)

/-- A write to one thread's TCB. -/
theorem updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) : tcbsKept st (st.updateTcb tid f) := fun t hT => by
  by_cases h : t.toObjId = tid.toObjId
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hT
    have ht : t = tid := SeLe4n.ThreadId.toObjId_injective _ _ h
    subst ht
    rw [SystemState.updateTcb_getTcb?_self st t f hInv, hx]; rfl
  · rw [SystemState.updateTcb_getTcb?_ne st tid f hInv t fun h' => h h'.symm]; exact hT

/-- A TCB stored over a slot. -/
theorem rewriteObject_tcb (st : SystemState) (x : SeLe4n.ObjId) (t' : TCB)
    (h : st.rewriteAdmissible x (.tcb t')) (hInv : st.objects.invExt) :
    tcbsKept st (st.rewriteObject x (.tcb t') h) := fun t hT => by
  by_cases hx : x = t.toObjId
  · subst hx; unfold SystemState.getTcb?
    rw [SystemState.rewriteObject_objects_self st _ _ h hInv]; rfl
  · rw [SystemState.rewriteObject_getTcb?_ne st x _ h hInv t hx]; exact hT

/-- An object other than a TCB stored over a slot holding none. -/
theorem rewriteObject_nonTcb (st : SystemState) (x : SeLe4n.ObjId) (o : KernelObject)
    (h : st.rewriteAdmissible x o) (hInv : st.objects.invExt)
    (hx : ∀ t, x = t.toObjId → st.getTcb? t = none) :
    tcbsKept st (st.rewriteObject x o h) := fun t hT => by
  by_cases hxt : x = t.toObjId
  · rw [hx t hxt] at hT; cases hT
  · rw [SystemState.rewriteObject_getTcb?_ne st x _ h hInv t hxt]; exact hT

/-- The frame a step keeps for the residents of the other cores. -/
theorem residentTcbKept {e : CoreId} {pre post : SystemState} (h : tcbsKept pre post) :
    residentTcbKeptOffCore e pre post :=
  residentTcbKeptOffCore_of_present h

end tcbsKept

/-- A step covers, lowers no remote flag and makes no thread current or
resident on a remote core: the unit the arm proofs chain. -/
structure stepCovers (e : CoreId) (pre post : SystemState) : Prop where
  covers : reschedulePendingCovers e pre post
  mono : reschedulePendingMonotone e pre post
  /-- WS-ZA ZA6.8: the cross-core frame of the current slots. -/
  currentKept : currentKeptOffCore e pre post
  /-- WS-ZA ZA6.10: the cross-core frame of the residency records. -/
  residentKept : residentKeptOffCore e pre post
  /-- WS-ZA ZA6.13: the cross-core frame of the register banks. -/
  banksKept : banksKeptOffCore e pre post
  /-- WS-ZA ZA6.21: the cross-core frame of the residents' TCBs. -/
  residentTcbKept : residentTcbKeptOffCore e pre post

theorem stepCovers_refl (e : CoreId) (st : SystemState) : stepCovers e st st :=
  ⟨reschedulePendingCovers_refl e st, reschedulePendingMonotone_refl e st,
    currentKeptOffCore_refl e st, residentKeptOffCore_refl e st, banksKeptOffCore_refl e st,
    residentTcbKeptOffCore_refl e st⟩

theorem stepCovers_trans {e : CoreId} {a b d : SystemState}
    (h₁ : stepCovers e a b) (h₂ : stepCovers e b d) : stepCovers e a d :=
  ⟨reschedulePendingCovers_trans h₁.1 h₂.1 h₂.2,
   reschedulePendingMonotone_trans h₁.2 h₂.2, currentKeptOffCore_trans h₁.3 h₂.3,
   residentKeptOffCore_trans h₁.4 h₂.4, banksKeptOffCore_trans h₁.5 h₂.5,
   residentTcbKeptOffCore_trans h₁.6 h₂.6 h₂.4⟩

theorem stepCovers_of_eq {e : CoreId} {pre post : SystemState} (h : post = pre) :
    stepCovers e pre post := h ▸ stepCovers_refl e pre

/-- **A step that moves no key input, no remote slot and no remote flag down
covers.**  The discharge for every object-only step. -/
theorem stepCovers_of_frame {e : CoreId} {pre post : SystemState}
    (hView : ∀ t, schedKeyView post t = schedKeyView pre t)
    (hElig : ∀ t, budgetEligibleView post t = budgetEligibleView pre t)
    (hRq : ∀ c, c ≠ e → ∀ t, post.queuedOn c t = true → pre.queuedOn c t = true)
    (hCur : ∀ c, c ≠ e → post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c)
    (hMono : reschedulePendingMonotone e pre post)
    (hRes : post.machine.residentCode = pre.machine.residentCode := by resident_frame)
    (hBank : banksKeptOffCore e pre post := by bank_kept) :
    stepCovers e pre post :=
  ⟨reschedulePendingCovers_of_frame hView hElig (fun c hc => Or.inr ⟨hRq c hc, hCur c hc⟩), hMono,
    currentKeptOffCore_of_eq hCur, residentKeptOffCore_of_eq hRes, hBank,
    (tcbsKept.of_views hView).residentTcbKept⟩

/-- The common shape: the scheduler is unchanged but for the flags, which only
rise. -/
theorem stepCovers_of_scheduler_eq_except_reschedule {e : CoreId} {pre post : SystemState}
    (hKeys : keyInputsEq pre post)
    (hSched : post.scheduler =
      { pre.scheduler with reschedulePending := post.scheduler.reschedulePending })
    (hMono : reschedulePendingMonotone e pre post)
    (hRes : post.machine.residentCode = pre.machine.residentCode := by resident_frame)
    (hBank : banksKeptOffCore e pre post := by bank_kept) :
    stepCovers e pre post :=
  stepCovers_of_frame (schedKeyView_eq_of_keyInputsEq hKeys)
    (budgetEligibleView_eq_of_keyInputsEq hKeys)
    (fun c _ t ht => (hKeys.runCoresAgree.queuedOn c t) ▸ ht) (fun c _ => by rw [hSched]; rfl) hMono
    hRes hBank

theorem reschedulePendingMonotone_of_scheduler_eq {e : CoreId} {pre post : SystemState}
    (h : post.scheduler = pre.scheduler) : reschedulePendingMonotone e pre post :=
  fun _ _ hp => by rw [h]; exact hp

/-- A scheduler-silent step moving no key input covers. -/
theorem stepCovers_of_scheduler_eq {e : CoreId} {pre post : SystemState}
    (hKeys : keyInputsEq pre post) (hSched : post.scheduler = pre.scheduler)
    (hRes : post.machine.residentCode = pre.machine.residentCode := by resident_frame)
    (hBank : banksKeptOffCore e pre post := by bank_kept) :
    stepCovers e pre post :=
  stepCovers_of_scheduler_eq_except_reschedule hKeys (by rw [hSched])
    (reschedulePendingMonotone_of_scheduler_eq hSched) hRes hBank

/-- A scheduler-silent step moving no key input and no remote residency record
covers: the residency settle's record on the executing core. -/
theorem stepCovers_of_scheduler_eq_residentKept {e : CoreId} {pre post : SystemState}
    (hKeys : keyInputsEq pre post) (hSched : post.scheduler = pre.scheduler)
    (hResK : residentKeptOffCore e pre post)
    (hBank : banksKeptOffCore e pre post := by bank_kept) :
    stepCovers e pre post :=
  ⟨reschedulePendingCovers_of_frame (schedKeyView_eq_of_keyInputsEq hKeys)
    (budgetEligibleView_eq_of_keyInputsEq hKeys)
    (fun c _ => Or.inr ⟨fun t ht => (hKeys.runCoresAgree.queuedOn c t) ▸ ht, by rw [hSched]⟩),
   reschedulePendingMonotone_of_scheduler_eq hSched,
   currentKeptOffCore_of_eq fun c _ => by rw [hSched], hResK, hBank,
   (tcbsKept.of_keyInputsEq hKeys).residentTcbKept⟩

/-- Equal eligibility views keep a TCB a TCB. -/
theorem getTcb?_isSome_of_budgetEligibleView {pre post : SystemState} {t : SeLe4n.ThreadId}
    (h : budgetEligibleView post t = budgetEligibleView pre t) {x : TCB}
    (hT : pre.getTcb? t = some x) : (post.getTcb? t).isSome := by
  have := congrArg Option.isSome h
  simp only [budgetEligibleView, Option.isSome_map, hT] at this
  rw [this]; rfl

/-- **A key write on `tid` followed by the key hook covers**: the write moved no
other key input, did not make `tid` budget-eligible, every remote core is
flagged or kept its slots (a queue may only shrink), and no remote flag
dropped. -/
theorem stepCovers_markKeyChangeFor {e : CoreId} {pre mid : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hPre : pre.getTcb? tid = some tcb)
    (hKeys : keyInputsEqExcept tid pre mid)
    (hSelf : candidacyNotGained pre mid tid)
    (hSlots : ∀ c, c ≠ e → mid.scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, mid.queuedOn c t = true → pre.queuedOn c t = true) ∧
        mid.scheduler.currentOnCore c = pre.scheduler.currentOnCore c))
    (hMono : reschedulePendingMonotone e pre mid) (hKept : currentKeptOffCore e pre mid)
    (hTid : (mid.getTcb? tid).isSome)
    (hResK : residentKeptOffCore e pre mid := by resident_kept)
    (hBank : banksKeptOffCore e pre mid := by bank_kept) :
    stepCovers e pre (markKeyChangeFor mid tid (effectiveSchedParams pre tcb)) :=
  ⟨markKeyChangeFor_covers hPre (fun _ ht => schedKeyView_eq_of_keyInputsEqExcept hKeys ht)
    (fun _ _ _ t _ => by
      by_cases ht : t = tid
      · subst ht; exact hSelf
      · exact candidacyNotGained_of_eq (budgetEligibleView_eq_of_keyInputsEqExcept hKeys ht).symm)
    hSlots,
   fun c hc h => markKeyChangeFor_reschedulePendingOnCore_mono _ _ _ _ (hMono c hc h),
   fun c hc t ht => hKept c hc t (by rwa [markKeyChangeFor_currentOnCore] at ht),
   fun c hc t ht => hResK c hc t (by rwa [markKeyChangeFor_machine] at ht),
   fun c hc => by rw [markKeyChangeFor_machine]; exact hBank c hc,
   fun c hc t ht hT => by
     rw [markKeyChangeFor_getTcb?]
     exact tcbsKept.of_keysExcept hKeys hTid t hT⟩

/-! ### The coverage reads what the chooser reads

The views the coverage compares (`schedKeyView`, `budgetEligibleView`) are the
whole of what the reschedule decision reads of a thread: the chooser
(`chooseBestRunnableEffective`) reads a walked thread's TCB presence, its
domain, `hasSufficientBudget` and `resolveEffectivePrioDeadline`; the gate
(`candidateOutranksCurrentOnCore`, `currentOutsideActiveDomainOnCore`) reads the
current thread's and the candidate's resolved key and the current's domain.
Each theorem below states that reading as a congruence, so a component the
views left out would fail to prove here rather than drift.  (The dispatch's
affinity check reads `cpuAffinity`, which the run-queue placement invariant
`runQueueAffinityConsistentOnCore` makes true of every queued candidate.) -/

/-- Equal key views: both TCBs absent, or both present with the same resolved
key and domain. -/
theorem schedKeyView_eq_cases {st st' : SystemState} {t : SeLe4n.ThreadId}
    (h : schedKeyView st' t = schedKeyView st t) :
    (st.getTcb? t = none ∧ st'.getTcb? t = none) ∨
    ∃ a b, st.getTcb? t = some a ∧ st'.getTcb? t = some b ∧
      resolveEffectivePrioDeadline st' b = resolveEffectivePrioDeadline st a ∧
      b.domain = a.domain := by
  cases ha : st.getTcb? t with
  | none =>
    left
    refine ⟨rfl, ?_⟩
    unfold schedKeyView at h; rw [ha] at h
    cases hb : st'.getTcb? t with
    | none => rfl
    | some _ => rw [hb] at h; simp at h
  | some a =>
    right
    cases hb : st'.getTcb? t with
    | none => unfold schedKeyView at h; rw [ha, hb] at h; simp at h
    | some b =>
      refine ⟨a, b, rfl, rfl, ?_⟩
      rw [schedKeyView_of_getTcb hb, schedKeyView_of_getTcb ha] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have h2' : (effectiveSchedParams st' b).2.1 = (effectiveSchedParams st a).2.1 := by
        revert h2
        generalize (effectiveSchedParams st' b).2.1 = x
        generalize (effectiveSchedParams st a).2.1 = y
        intro h2; cases x; cases y; simp_all
      refine ⟨?_, ?_⟩
      · rw [← effectiveSchedParams_priority_deadline_eq_resolve,
          ← effectiveSchedParams_priority_deadline_eq_resolve, h1, h2']
      · rw [← effectiveSchedParams_domain_eq st' b, ← effectiveSchedParams_domain_eq st a, h3]

/-- Equal eligibility views of two present TCBs: the same budget answer. -/
theorem hasSufficientBudget_eq_of_budgetEligibleView {st st' : SystemState}
    {t : SeLe4n.ThreadId} {a b : TCB} (ha : st.getTcb? t = some a) (hb : st'.getTcb? t = some b)
    (h : budgetEligibleView st' t = budgetEligibleView st t) :
    hasSufficientBudget st' b = hasSufficientBudget st a := by
  unfold budgetEligibleView at h; rw [ha, hb] at h; simpa using h

/-- **The chooser reads the views.**  Over a walk whose threads agree on both
views (and on the caller's filter), the budget-aware scan returns the same
answer. -/
theorem chooseBestRunnableEffective_eq_of_views {st st' : SystemState}
    {el el' : TCB → Bool} :
    ∀ (l : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)),
      (∀ t ∈ l, schedKeyView st' t = schedKeyView st t ∧
        budgetEligibleView st' t = budgetEligibleView st t ∧
        ∀ a b, st.getTcb? t = some a → st'.getTcb? t = some b → el' b = el a) →
      chooseBestRunnableEffective st' el' l best = chooseBestRunnableEffective st el l best
  | [], _, _ => rfl
  | t :: rest, best, h => by
    obtain ⟨hK, hE, hEl⟩ := h t (List.mem_cons_self ..)
    have hRest := fun x hx => h x (List.mem_cons_of_mem _ hx)
    unfold chooseBestRunnableEffective
    rcases schedKeyView_eq_cases hK with ⟨ha, hb⟩ | ⟨a, b, ha, hb, hR, -⟩
    · simp only [ha, hb]
      exact chooseBestRunnableEffective_eq_of_views rest best hRest
    · simp only [ha, hb, hEl a b ha hb, hasSufficientBudget_eq_of_budgetEligibleView ha hb hE, hR]
      exact chooseBestRunnableEffective_eq_of_views rest _ hRest

/-- The domain-filtered scan reads the views and the active domain alone (the
filter reads the domain the key view carries). -/
theorem chooseBestRunnableInDomainEffective_eq_of_views {st st' : SystemState}
    (l : List SeLe4n.ThreadId) (dom : SeLe4n.DomainId)
    (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (h : ∀ t ∈ l, schedKeyView st' t = schedKeyView st t ∧
      budgetEligibleView st' t = budgetEligibleView st t) :
    chooseBestRunnableInDomainEffective st' l dom best =
      chooseBestRunnableInDomainEffective st l dom best := by
  unfold chooseBestRunnableInDomainEffective
  refine chooseBestRunnableEffective_eq_of_views l best fun t ht => ⟨(h t ht).1, (h t ht).2, ?_⟩
  intro a b ha hb
  rcases schedKeyView_eq_cases (h t ht).1 with ⟨ha', -⟩ | ⟨a', b', ha', hb', -, hD⟩
  · rw [ha] at ha'; cases ha'
  · rw [ha] at ha'; rw [hb] at hb'; cases ha'; cases hb'; rw [hD]

/-- **Core `c`'s selection reads the views**: equal walks, an equal active
domain, and walked threads equal on both views give the same choice. -/
theorem chooseThreadEffectiveOnCore_eq_of_views {st st' : SystemState} {c : CoreId}
    (hMax : st'.runMaxBucketWalk c = st.runMaxBucketWalk c)
    (hAll : st'.runQueueWalk c = st.runQueueWalk c)
    (hDom : st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c)
    (hV : ∀ t, (t ∈ st.runMaxBucketWalk c ∨ t ∈ st.runQueueWalk c) →
      schedKeyView st' t = schedKeyView st t ∧
        budgetEligibleView st' t = budgetEligibleView st t) :
    chooseThreadEffectiveOnCore st' c = chooseThreadEffectiveOnCore st c := by
  unfold chooseThreadEffectiveOnCore chooseBestInWalksEffective
  rw [hMax, hAll, hDom,
    chooseBestRunnableInDomainEffective_eq_of_views _ _ _ fun t ht => hV t (Or.inl ht),
    chooseBestRunnableInDomainEffective_eq_of_views (st.runQueueWalk c) _ _
      fun t ht => hV t (Or.inr ht)]

/-- **The preemption gate reads the key views** of the current thread and the
candidate. -/
theorem candidateOutranksCurrentOnCore_eq_of_views {st st' : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hCurV : ∀ t, st.scheduler.currentOnCore c = some t → schedKeyView st' t = schedKeyView st t)
    (hTid : schedKeyView st' tid = schedKeyView st tid) :
    candidateOutranksCurrentOnCore st' c tid = candidateOutranksCurrentOnCore st c tid := by
  unfold candidateOutranksCurrentOnCore
  rw [hCur]
  cases hc : st.scheduler.currentOnCore c with
  | none => rfl
  | some cur =>
    rcases schedKeyView_eq_cases (hCurV cur hc) with ⟨ha, hb⟩ | ⟨a, b, ha, hb, hR, -⟩
    · simp only [ha, hb]
    · rcases schedKeyView_eq_cases hTid with ⟨ha', hb'⟩ | ⟨a', b', ha', hb', hR', -⟩
      · simp only [ha, hb, ha', hb']
      · simp only [ha, hb, ha', hb', hR, hR']

/-- **The domain-drop check reads the current thread's key view.** -/
theorem currentOutsideActiveDomainOnCore_eq_of_views {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hCurV : ∀ t, st.scheduler.currentOnCore c = some t → schedKeyView st' t = schedKeyView st t)
    (hDom : st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c) :
    currentOutsideActiveDomainOnCore st' c = currentOutsideActiveDomainOnCore st c := by
  unfold currentOutsideActiveDomainOnCore
  rw [hCur, hDom]
  cases hc : st.scheduler.currentOnCore c with
  | none => rfl
  | some cur =>
    rcases schedKeyView_eq_cases (hCurV cur hc) with ⟨ha, hb⟩ | ⟨a, b, ha, hb, -, hD⟩
    · simp only [ha, hb]
    · simp only [ha, hb, hD]


end SeLe4n.Kernel
