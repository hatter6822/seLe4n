-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingEntry

/-!
# The routed entry's report word

The routed syscall entry (`syscallEntryCheckedK`) runs each syscall's arm out
of line, one function per route (`RoutedArms`), so the kernel is compiled once
per arm and never once per entry.  An arm's boundary carries machine words and
the state passed owned, and its result is the state alone: a returned record,
`Except` or pair would be a heap cell on every syscall.  What the arm decided
-- which continuation of the continued entry its result is for, and whether it
committed or refused, with which error -- is a small code the arm pushes onto
the state's report word (`MachineState.entryReport`) and the entry pops.

The push is a multiplication and an addition, the pop a division, so a push
followed by its pop is the identity on every state, whatever the word held
before (`popEntryReport_pushEntryReport`): the state the entry continues with
is the arm's own, and no frame property of any arm is needed for it.  Every
committed state holds what its entry was handed (`0` from boot), so the word
stays a small number and its arithmetic boxes nothing.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The report word's radix: one code below it per push.  A code is the
continuation's kind (`0` the entry's own refusals and the routes with no
operand, `1` an operand arm's result, `2` an operand's failed resolution) plus
four times the error's constructor index plus one, or the kind alone for a
committed result (`entryReportError_lt`). -/
def entryReportBase : Nat := 256

/-- **Push** `code` onto the state's report word.  Out of line, so each arm's
many result sites call it with the state they hold, which it updates in
place. -/
@[noinline] def _root_.SeLe4n.Model.SystemState.pushEntryReport (code : Nat) (st : SystemState) : SystemState :=
  { st with machine := { st.machine with
      entryReport := st.machine.entryReport * entryReportBase + code } }

/-- The code on top of the state's report word. -/
@[inline] def _root_.SeLe4n.Model.SystemState.entryReportCode (st : SystemState) : Nat :=
  st.machine.entryReport % entryReportBase

/-- **Pop** the state's report word: the word the push found. -/
@[noinline] def _root_.SeLe4n.Model.SystemState.popEntryReport (st : SystemState) : SystemState :=
  { st with machine := { st.machine with
      entryReport := st.machine.entryReport / entryReportBase } }

theorem _root_.SeLe4n.Model.SystemState.entryReportCode_pushEntryReport {code : Nat} (st : SystemState)
    (h : code < entryReportBase) :
    (st.pushEntryReport code).entryReportCode = code := by
  simp only [SystemState.entryReportCode, SystemState.pushEntryReport]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt h

/-- **A push followed by its pop is the identity**, on every state. -/
theorem _root_.SeLe4n.Model.SystemState.popEntryReport_pushEntryReport {code : Nat} (st : SystemState)
    (h : code < entryReportBase) :
    (st.pushEntryReport code).popEntryReport = st := by
  have hb : 0 < entryReportBase := by decide
  have hq : (st.machine.entryReport * entryReportBase + code) / entryReportBase =
      st.machine.entryReport := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt h, Nat.zero_add]
  simp only [SystemState.popEntryReport, SystemState.pushEntryReport, hq]

/-- Every error's constructor index is below 63, so its code is below the
radix. -/
theorem _root_.SeLe4n.Model.KernelError.ctorIdx_lt (e : KernelError) : e.ctorIdx < 63 := by
  cases e <;> decide

/-- The code of a committed result for continuation `kind`. -/
@[inline] def entryReportOk (kind : Nat) : Nat := kind

/-- The code of a refusal with `e` for continuation `kind`. -/
@[inline] def entryReportError (kind : Nat) (e : KernelError) : Nat :=
  kind + 4 * (e.ctorIdx + 1)

theorem entryReportError_lt {kind : Nat} (hk : kind < 4) (e : KernelError) :
    entryReportError kind e < entryReportBase := by
  have := KernelError.ctorIdx_lt e
  unfold entryReportError entryReportBase
  omega

/-- The continued entry's first continuation, as a report: a committed state
or a refusal, pushed under kind `0`. -/
@[inline] def entryReportGeneral
    (r : Except (KernelError × SystemState) (Unit × SystemState)) : SystemState :=
  match r with
  | .ok ((), s) => s.pushEntryReport (entryReportOk 0)
  | .error (e, s) => s.pushEntryReport (entryReportError 0 e)

/-- The continued entry's second continuation, an operand arm's result, as a
report under kind `1`. -/
@[inline] def entryReportResolved
    (r : Except (KernelError × SystemState) (Unit × SystemState)) : SystemState :=
  match r with
  | .ok ((), s) => s.pushEntryReport (entryReportOk 1)
  | .error (e, s) => s.pushEntryReport (entryReportError 1 e)

/-- The continued entry's third continuation, an operand's failed resolution,
as a report under kind `2`; the syscall and the operand's address are the
route's, which the entry holds. -/
@[inline] def entryReportLookup (e : KernelError) (s : SystemState) : SystemState :=
  s.pushEntryReport (entryReportError 2 e)

/-- **The report, handed on**: pop the arm's code and hand its state to the
continuation the code names, as the arm's result would have been handed. -/
@[inline] def entryReportOutcome {β : Type}
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : KernelError → SystemState → β) (s : SystemState) : β :=
  let c := s.entryReportCode
  let s' := s.popEntryReport
  if c < 4 then
    if c = 1 then kRes (.ok ((), s')) else kGen (.ok ((), s'))
  else
    let e := KernelError.ofNat (c / 4 - 1)
    if c % 4 = 0 then kGen (.error (e, s'))
    else if c % 4 = 1 then kRes (.error (e, s'))
    else kLook e s'

private theorem entryReportError_div (kind : Nat) (hk : kind < 4) (e : KernelError) :
    entryReportError kind e / 4 - 1 = e.ctorIdx ∧ entryReportError kind e % 4 = kind ∧
      ¬ entryReportError kind e < 4 := by
  unfold entryReportError
  omega

theorem entryReportOutcome_general {β : Type}
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) :
    entryReportOutcome kGen kRes kLook (entryReportGeneral r) = kGen r := by
  rcases r with ⟨e, s⟩ | ⟨⟨⟩, s⟩
  · obtain ⟨h1, h2, h3⟩ := entryReportError_div 0 (by decide) e
    have hl := entryReportError_lt (kind := 0) (by decide) e
    simp only [entryReportOutcome, entryReportGeneral, s.entryReportCode_pushEntryReport hl,
      s.popEntryReport_pushEntryReport hl, h1, h2, h3, KernelError.ofNat_ctorIdx, if_false,
      if_true]
  · have hl : (0 : Nat) < entryReportBase := by decide
    simp only [entryReportOutcome, entryReportGeneral, entryReportOk,
      s.entryReportCode_pushEntryReport hl, s.popEntryReport_pushEntryReport hl]
    simp

theorem entryReportOutcome_resolved {β : Type}
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) :
    entryReportOutcome kGen kRes kLook (entryReportResolved r) = kRes r := by
  rcases r with ⟨e, s⟩ | ⟨⟨⟩, s⟩
  · obtain ⟨h1, h2, h3⟩ := entryReportError_div 1 (by decide) e
    have hl := entryReportError_lt (kind := 1) (by decide) e
    simp only [entryReportOutcome, entryReportResolved, s.entryReportCode_pushEntryReport hl,
      s.popEntryReport_pushEntryReport hl, h1, h2, h3, KernelError.ofNat_ctorIdx, if_false,
      if_true]
    rfl
  · have hl : (1 : Nat) < entryReportBase := by decide
    simp only [entryReportOutcome, entryReportResolved, entryReportOk,
      s.entryReportCode_pushEntryReport hl, s.popEntryReport_pushEntryReport hl]
    simp

theorem entryReportOutcome_lookup {β : Type}
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : KernelError → SystemState → β) (e : KernelError) (s : SystemState) :
    entryReportOutcome kGen kRes kLook (entryReportLookup e s) = kLook e s := by
  obtain ⟨h1, h2, h3⟩ := entryReportError_div 2 (by decide) e
  have hl := entryReportError_lt (kind := 2) (by decide) e
  simp only [entryReportOutcome, entryReportLookup, s.entryReportCode_pushEntryReport hl,
    s.popEntryReport_pushEntryReport hl, h1, h2, h3, KernelError.ofNat_ctorIdx, if_false]
  rfl

/-- **`dispatchOperandCheckedK` commutes with a function of its result**: a
function of what it hands on is what it hands on to the continuations composed
with that function.  The routed arms run it into the report continuations and
the entry hands the report on, so this is what makes the two runs one. -/
theorem dispatchOperandCheckedK_map {β γ : Type} (g : β → γ) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β) :
    g (dispatchOperandCheckedK sid capAddr tid executingCore arm st kPre kArm onLookup) =
      dispatchOperandCheckedK sid capAddr tid executingCore arm st (fun r => g (kPre r))
        (fun r => g (kArm r)) (fun e s => g (onLookup e s)) := by
  unfold dispatchOperandCheckedK
  split
  · rfl
  split
  · split
    · simp only [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
      split
      · rfl
      · split
        · rfl
        · split <;> (unfold noCapRefusal; split <;> (try split) <;> rfl)
    all_goals rfl
  all_goals rfl

/-- **`longOperandK` commutes with a function of its result**, as
`dispatchOperandCheckedK` does. -/
theorem longOperandK_map {β γ : Type} (g : β → γ) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (n : Nat) (st : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β) :
    g (longOperandK sid capAddr tid executingCore arm n st kPre kArm onLookup) =
      longOperandK sid capAddr tid executingCore arm n st (fun r => g (kPre r))
        (fun r => g (kArm r)) (fun e s => g (onLookup e s)) := by
  unfold longOperandK dispatchOperandFilledK
  exact dispatchOperandCheckedK_map g _ _ _ _ _ _ _ _ _

/-- **`overflowOneOperandK` commutes with a function of its result**. -/
theorem overflowOneOperandK_map {β γ : Type} (g : β → γ) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β) :
    g (overflowOneOperandK sid capAddr tid executingCore arm st kPre kArm onLookup) =
      overflowOneOperandK sid capAddr tid executingCore arm st (fun r => g (kPre r))
        (fun r => g (kArm r)) (fun e s => g (onLookup e s)) := by
  unfold overflowOneOperandK dispatchOperandFilledK
  exact dispatchOperandCheckedK_map g _ _ _ _ _ _ _ _ _

end SeLe4n.Kernel
