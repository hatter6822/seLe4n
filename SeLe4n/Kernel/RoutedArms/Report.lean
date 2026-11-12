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
the state's report word (`MachineState.entryReport`) and the entry pops.  A
refusal's payload rides beside the code as its five payload words, one stack
per word (`MachineState.entryReportWord0`–`4`), so the entry hands a refusal
on as its discriminant and words (`entryReportOutcomeW`) and builds no error
(D2b).

The push is a multiplication and an addition, the pop a division, so a push
followed by its pop is the identity on every state, whatever the word held
before (`popEntryReport_pushEntryReport`): the state the entry continues with
is the arm's own, and no frame property of any arm is needed for it.  Every
committed state holds what its entry was handed (`0` from boot), so the word
stays a small number and its arithmetic boxes nothing; a payload stack pushed
from empty holds the word itself (`reportStackPushFast`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The report word's radix: one code below it per push.  A code is the
continuation's kind (`0` the entry's own refusals and the routes with no
operand, `1` an operand arm's result, `2` an operand's failed resolution) plus
four times the error's discriminant plus one, or the kind alone for a
committed result (`entryReportError_lt`). -/
def entryReportBase : Nat := 256

/-- The payload stacks' radix: one machine word per push. -/
def entryReportWordBase : Nat := 2 ^ 64

/-- Push the word `w` onto the payload stack `a`. -/
def reportStackPush (a : Nat) (w : UInt64) : Nat := a * entryReportWordBase + w.toNat

/-- `reportStackPush` as it runs: onto an empty stack, the word itself, with no
multiplication by the radix (a number past a machine word). -/
def reportStackPushFast (a : Nat) (w : UInt64) : Nat :=
  if a = 0 then w.toNat else a * entryReportWordBase + w.toNat

@[csimp] theorem reportStackPush_eq_fast : @reportStackPush = @reportStackPushFast := by
  funext a w
  unfold reportStackPush reportStackPushFast
  split <;> simp_all

/-- Pop the payload stack `a`. -/
def reportStackPop (a : Nat) : Nat := a / entryReportWordBase

/-- `reportStackPop` as it runs: a stack holding one word pops to empty with no
division by the radix. -/
def reportStackPopFast (a : Nat) : Nat :=
  if a < entryReportWordBase then 0 else a / entryReportWordBase

@[csimp] theorem reportStackPop_eq_fast : @reportStackPop = @reportStackPopFast := by
  funext a
  unfold reportStackPop reportStackPopFast
  split
  · next h => exact Nat.div_eq_of_lt h
  · rfl

theorem reportStackPop_push (a : Nat) (w : UInt64) : reportStackPop (reportStackPush a w) = a := by
  have hw : w.toNat < entryReportWordBase := w.toNat_lt
  have hb : 0 < entryReportWordBase := by decide
  unfold reportStackPop reportStackPush
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hw, Nat.zero_add]

theorem reportStackPush_top (a : Nat) (w : UInt64) : UInt64.ofNat (reportStackPush a w) = w := by
  unfold reportStackPush entryReportWordBase
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt w.toNat_lt]

/-- **Push** `code` and the payload words `w0`–`w4` onto the state's report.
Out of line, so each arm's many result sites call it with the state they hold,
which it updates in place. -/
@[noinline] def _root_.SeLe4n.Model.SystemState.pushEntryReport (code : Nat)
    (w0 w1 w2 w3 w4 : UInt64) (st : SystemState) : SystemState :=
  { st with machine := { st.machine with
      entryReport := st.machine.entryReport * entryReportBase + code
      entryReportWord0 := reportStackPush st.machine.entryReportWord0 w0
      entryReportWord1 := reportStackPush st.machine.entryReportWord1 w1
      entryReportWord2 := reportStackPush st.machine.entryReportWord2 w2
      entryReportWord3 := reportStackPush st.machine.entryReportWord3 w3
      entryReportWord4 := reportStackPush st.machine.entryReportWord4 w4 } }

/-- The code on top of the state's report word. -/
@[inline] def _root_.SeLe4n.Model.SystemState.entryReportCode (st : SystemState) : Nat :=
  st.machine.entryReport % entryReportBase

/-- **Pop** the state's report: the word and the stacks the push found. -/
@[noinline] def _root_.SeLe4n.Model.SystemState.popEntryReport (st : SystemState) : SystemState :=
  { st with machine := { st.machine with
      entryReport := st.machine.entryReport / entryReportBase
      entryReportWord0 := reportStackPop st.machine.entryReportWord0
      entryReportWord1 := reportStackPop st.machine.entryReportWord1
      entryReportWord2 := reportStackPop st.machine.entryReportWord2
      entryReportWord3 := reportStackPop st.machine.entryReportWord3
      entryReportWord4 := reportStackPop st.machine.entryReportWord4 } }

theorem _root_.SeLe4n.Model.SystemState.entryReportCode_pushEntryReport {code : Nat}
    {w0 w1 w2 w3 w4 : UInt64} (st : SystemState) (h : code < entryReportBase) :
    (st.pushEntryReport code w0 w1 w2 w3 w4).entryReportCode = code := by
  simp only [SystemState.entryReportCode, SystemState.pushEntryReport]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt h

/-- The payload words on top of the report, as the push put them. -/
theorem _root_.SeLe4n.Model.SystemState.entryReportWords_pushEntryReport {code : Nat}
    {w0 w1 w2 w3 w4 : UInt64} (st : SystemState) :
    let s := st.pushEntryReport code w0 w1 w2 w3 w4
    UInt64.ofNat s.machine.entryReportWord0 = w0 ∧ UInt64.ofNat s.machine.entryReportWord1 = w1 ∧
      UInt64.ofNat s.machine.entryReportWord2 = w2 ∧
      UInt64.ofNat s.machine.entryReportWord3 = w3 ∧
      UInt64.ofNat s.machine.entryReportWord4 = w4 := by
  simp only [SystemState.pushEntryReport, reportStackPush_top, and_self]

/-- **A push followed by its pop is the identity**, on every state. -/
theorem _root_.SeLe4n.Model.SystemState.popEntryReport_pushEntryReport {code : Nat}
    {w0 w1 w2 w3 w4 : UInt64} (st : SystemState) (h : code < entryReportBase) :
    (st.pushEntryReport code w0 w1 w2 w3 w4).popEntryReport = st := by
  have hb : 0 < entryReportBase := by decide
  have hq : (st.machine.entryReport * entryReportBase + code) / entryReportBase =
      st.machine.entryReport := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt h, Nat.zero_add]
  simp only [SystemState.popEntryReport, SystemState.pushEntryReport, hq, reportStackPop_push]

/-- The code of a committed result for continuation `kind`. -/
@[inline] def entryReportOk (kind : Nat) : Nat := kind

/-- The code of a refusal with `e` for continuation `kind`. -/
@[inline] def entryReportError (kind : Nat) (e : KernelError) : Nat :=
  kind + 4 * (e.toDiscriminant + 1)

theorem entryReportError_lt {kind : Nat} (hk : kind < 4) (e : KernelError) :
    entryReportError kind e < entryReportBase := by
  have := KernelError.toDiscriminant_lt e
  unfold entryReportError entryReportBase
  unfold KernelError.kernelErrorEncodingBound at this
  omega

/-- Push a committed result for continuation `kind`: its code and no payload. -/
@[inline] def entryReportPushOk (kind : Nat) (s : SystemState) : SystemState :=
  s.pushEntryReport (entryReportOk kind) 0 0 0 0 0

/-- Push a refusal with `e` for continuation `kind`: its code and its payload
words, as scalars (D2b). -/
@[inline] def entryReportPushError (kind : Nat) (e : KernelError) (s : SystemState) : SystemState :=
  s.pushEntryReport (entryReportError kind e) (e.payloadWord 0) (e.payloadWord 1)
    (e.payloadWord 2) (e.payloadWord 3) (e.payloadWord 4)

/-- The continued entry's first continuation, as a report: a committed state
or a refusal, pushed under kind `0`. -/
@[inline] def entryReportGeneral
    (r : Except (KernelError × SystemState) (Unit × SystemState)) : SystemState :=
  match r with
  | .ok ((), s) => entryReportPushOk 0 s
  | .error (e, s) => entryReportPushError 0 e s

/-- The continued entry's second continuation, an operand arm's result, as a
report under kind `1`. -/
@[inline] def entryReportResolved
    (r : Except (KernelError × SystemState) (Unit × SystemState)) : SystemState :=
  match r with
  | .ok ((), s) => entryReportPushOk 1 s
  | .error (e, s) => entryReportPushError 1 e s

/-- The continued entry's third continuation, an operand's failed resolution,
as a report under kind `2`; the syscall and the operand's address are the
route's, which the entry holds. -/
@[inline] def entryReportLookup (e : KernelError) (s : SystemState) : SystemState :=
  entryReportPushError 2 e s

/-- A continuation on results given as its committed half and its refusal half,
the refusal taken as its discriminant and payload words. -/
@[inline] def liftReport {β : Type} (kOk : SystemState → β)
    (kErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) : β :=
  match r with
  | .ok ((), s) => kOk s
  | .error (e, s) =>
    kErr e.toDiscriminant (e.payloadWord 0) (e.payloadWord 1) (e.payloadWord 2)
      (e.payloadWord 3) (e.payloadWord 4) s

/-- **The report, handed on as words**: pop the arm's code and payload words
and hand its state to the continuation the code names — a refusal as its
discriminant and payload words, so no error is built (D2b); an operand's
failed resolution as the error itself. -/
@[inline] def entryReportOutcomeW {β : Type} (kGenOk kResOk : SystemState → β)
    (kGenErr kResErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (kLook : KernelError → SystemState → β) (s : SystemState) : β :=
  let c := s.entryReportCode
  let w0 := UInt64.ofNat s.machine.entryReportWord0
  let w1 := UInt64.ofNat s.machine.entryReportWord1
  let w2 := UInt64.ofNat s.machine.entryReportWord2
  let w3 := UInt64.ofNat s.machine.entryReportWord3
  let w4 := UInt64.ofNat s.machine.entryReportWord4
  let s' := s.popEntryReport
  if c < 4 then
    if c = 1 then kResOk s' else kGenOk s'
  else
    let d := c / 4 - 1
    if c % 4 = 0 then kGenErr d w0 w1 w2 w3 w4 s'
    else if c % 4 = 1 then kResErr d w0 w1 w2 w3 w4 s'
    else kLook (KernelError.ofPayloadWords d w0 w1 w2 w3 w4) s'

/-- **The report, handed on**: `entryReportOutcomeW` into continuations on
results, each refusal rebuilt from its words. -/
@[inline] def entryReportOutcome {β : Type}
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : KernelError → SystemState → β) (s : SystemState) : β :=
  entryReportOutcomeW (fun s => kGen (.ok ((), s))) (fun s => kRes (.ok ((), s)))
    (fun d w0 w1 w2 w3 w4 s => kGen (.error (KernelError.ofPayloadWords d w0 w1 w2 w3 w4, s)))
    (fun d w0 w1 w2 w3 w4 s => kRes (.error (KernelError.ofPayloadWords d w0 w1 w2 w3 w4, s)))
    kLook s

/-- Lifting a continuation's halves, each refusal rebuilt from its words, is
the continuation. -/
theorem liftReport_ofPayloadWords {β : Type}
    (k : Except (KernelError × SystemState) (Unit × SystemState) → β) :
    liftReport (fun s => k (.ok ((), s)))
      (fun d w0 w1 w2 w3 w4 s => k (.error (KernelError.ofPayloadWords d w0 w1 w2 w3 w4, s))) = k := by
  funext r
  rcases r with ⟨e, s⟩ | ⟨⟨⟩, s⟩
  · simp only [liftReport, KernelError.ofPayloadWords_payloadWord]
  · rfl

private theorem entryReportError_div (kind : Nat) (hk : kind < 4) (e : KernelError) :
    entryReportError kind e / 4 - 1 = e.toDiscriminant ∧ entryReportError kind e % 4 = kind ∧
      ¬ entryReportError kind e < 4 := by
  unfold entryReportError
  omega

private theorem entryReportOutcomeW_pushError {β : Type} (kGenOk kResOk : SystemState → β)
    (kGenErr kResErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (kLook : KernelError → SystemState → β) (kind : Nat) (hk : kind < 4) (e : KernelError)
    (s : SystemState) :
    entryReportOutcomeW kGenOk kResOk kGenErr kResErr kLook (entryReportPushError kind e s) =
      (if kind = 0 then kGenErr e.toDiscriminant (e.payloadWord 0) (e.payloadWord 1)
          (e.payloadWord 2) (e.payloadWord 3) (e.payloadWord 4) s
       else if kind = 1 then kResErr e.toDiscriminant (e.payloadWord 0) (e.payloadWord 1)
          (e.payloadWord 2) (e.payloadWord 3) (e.payloadWord 4) s
       else kLook e s) := by
  obtain ⟨h1, h2, h3⟩ := entryReportError_div kind hk e
  have hl := entryReportError_lt hk e
  obtain ⟨hw0, hw1, hw2, hw3, hw4⟩ :=
    s.entryReportWords_pushEntryReport (code := entryReportError kind e) (w0 := e.payloadWord 0)
      (w1 := e.payloadWord 1) (w2 := e.payloadWord 2) (w3 := e.payloadWord 3)
      (w4 := e.payloadWord 4)
  simp only [entryReportOutcomeW, entryReportPushError, s.entryReportCode_pushEntryReport hl,
    s.popEntryReport_pushEntryReport hl, h1, h2, h3, hw0, hw1, hw2, hw3, hw4, if_false,
    KernelError.ofPayloadWords_payloadWord]

theorem entryReportOutcomeW_general {β : Type} (kGenOk kResOk : SystemState → β)
    (kGenErr kResErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (kLook : KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) :
    entryReportOutcomeW kGenOk kResOk kGenErr kResErr kLook (entryReportGeneral r) =
      liftReport kGenOk kGenErr r := by
  rcases r with ⟨e, s⟩ | ⟨⟨⟩, s⟩
  · simp only [entryReportGeneral, entryReportOutcomeW_pushError _ _ _ _ _ 0 (by decide),
      if_true, liftReport]
  · have hl : (0 : Nat) < entryReportBase := by decide
    simp only [entryReportOutcomeW, entryReportGeneral, entryReportPushOk, entryReportOk,
      s.entryReportCode_pushEntryReport hl, s.popEntryReport_pushEntryReport hl, liftReport]
    simp

theorem entryReportOutcomeW_resolved {β : Type} (kGenOk kResOk : SystemState → β)
    (kGenErr kResErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (kLook : KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) :
    entryReportOutcomeW kGenOk kResOk kGenErr kResErr kLook (entryReportResolved r) =
      liftReport kResOk kResErr r := by
  rcases r with ⟨e, s⟩ | ⟨⟨⟩, s⟩
  · simp only [entryReportResolved, entryReportOutcomeW_pushError _ _ _ _ _ 1 (by decide),
      liftReport]
    simp
  · have hl : (1 : Nat) < entryReportBase := by decide
    simp only [entryReportOutcomeW, entryReportResolved, entryReportPushOk, entryReportOk,
      s.entryReportCode_pushEntryReport hl, s.popEntryReport_pushEntryReport hl, liftReport]
    simp

theorem entryReportOutcomeW_lookup {β : Type} (kGenOk kResOk : SystemState → β)
    (kGenErr kResErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (kLook : KernelError → SystemState → β) (e : KernelError) (s : SystemState) :
    entryReportOutcomeW kGenOk kResOk kGenErr kResErr kLook (entryReportLookup e s) =
      kLook e s := by
  simp only [entryReportLookup, entryReportOutcomeW_pushError _ _ _ _ _ 2 (by decide)]
  simp

theorem entryReportOutcome_general {β : Type}
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) :
    entryReportOutcome kGen kRes kLook (entryReportGeneral r) = kGen r := by
  unfold entryReportOutcome
  rw [entryReportOutcomeW_general, liftReport_ofPayloadWords]

theorem entryReportOutcome_resolved {β : Type}
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) :
    entryReportOutcome kGen kRes kLook (entryReportResolved r) = kRes r := by
  unfold entryReportOutcome
  rw [entryReportOutcomeW_resolved, liftReport_ofPayloadWords]

theorem entryReportOutcome_lookup {β : Type}
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : KernelError → SystemState → β) (e : KernelError) (s : SystemState) :
    entryReportOutcome kGen kRes kLook (entryReportLookup e s) = kLook e s := by
  unfold entryReportOutcome
  rw [entryReportOutcomeW_lookup]

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
