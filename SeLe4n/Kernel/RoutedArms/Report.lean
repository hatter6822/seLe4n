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
(D2b).  A stack is its top word, an unboxed `UInt64` field, and the words
beneath it (`MachineState.entryReportBelow0`–`4`, radix `2^64`): a payload
word is a full machine word, and a `Nat` at or above `2^63` is a heap cell, so
no payload word on the refusal path is ever a `Nat`.

The push is a multiplication and an addition, the pop a division, so a push
followed by its pop is the identity on every state, whatever the word held
before (`popEntryReport_pushEntryReport`): the state the entry continues with
is the arm's own, and no frame property of any arm is needed for it.  Every
committed state holds what its entry was handed (`0` from boot), so the word
stays a small number and its arithmetic boxes nothing; the words beneath each
payload top stay `0`, which the push and the pop keep with no conversion
(`reportBelowPushFast`, `reportStackPopFast`).
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

/-- The words beneath a payload stack's top once `top` is pushed under a new
word: `top` joins the words `below` it, radix `2^64`.  The top itself stays a
`UInt64` field (`MachineState.entryReportWord0`), so a push never makes a
payload word a `Nat`; only a second report pushed over a first moves the first
one's word here. -/
def reportBelowPush (below : Nat) (top : UInt64) : Nat :=
  below * entryReportWordBase + top.toNat

/-- `reportBelowPush` as it runs.  Over an empty stack (`below = 0`, `top =
0`, every state the entry holds) it is `0` with no conversion at all; over a
pending report it takes `top` in its two 32-bit halves, each a scalar `Nat`,
so not even this path turns a full-width word into a `Nat` cell. -/
def reportBelowPushFast (below : Nat) (top : UInt64) : Nat :=
  if top = 0 ∧ below = 0 then 0
  else below * entryReportWordBase +
    ((top >>> 32).toNat * 2 ^ 32 + (top &&& 0xFFFFFFFF).toNat)

theorem uint64_toNat_halves (w : UInt64) :
    (w >>> 32).toNat * 2 ^ 32 + (w &&& 0xFFFFFFFF).toNat = w.toNat := by
  have h1 : (w >>> 32).toNat = w.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_shiftRight]
    simp [Nat.shiftRight_eq_div_pow]
  have h2 : (w &&& 0xFFFFFFFF).toNat = w.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_and]
    have : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := by decide
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
  rw [h1, h2, Nat.mul_comm]
  exact Nat.div_add_mod _ _

@[csimp] theorem reportBelowPush_eq_fast : @reportBelowPush = @reportBelowPushFast := by
  funext below top
  unfold reportBelowPush reportBelowPushFast
  rw [uint64_toNat_halves]
  split
  · next h => obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl
  · rfl

/-- Pop the words beneath a payload stack's top. -/
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

/-- The top word a pop restores from the words beneath it. -/
@[inline] def reportBelowTop (below : Nat) : UInt64 := UInt64.ofNat below

theorem reportStackPop_push (a : Nat) (w : UInt64) :
    reportStackPop (reportBelowPush a w) = a := by
  have hw : w.toNat < entryReportWordBase := w.toNat_lt
  have hb : 0 < entryReportWordBase := by decide
  unfold reportStackPop reportBelowPush
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hw, Nat.zero_add]

theorem reportBelowTop_push (a : Nat) (w : UInt64) : reportBelowTop (reportBelowPush a w) = w := by
  unfold reportBelowTop reportBelowPush entryReportWordBase
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt w.toNat_lt]

/-- **Push** `code` and the payload words `w0`–`w4` onto the state's report.
Out of line, so each arm's many result sites call it with the state they hold,
which it updates in place. -/
@[noinline] def _root_.SeLe4n.Model.SystemState.pushEntryReport (code : Nat)
    (w0 w1 w2 w3 w4 : UInt64) (st : SystemState) : SystemState :=
  { st with machine := { st.machine with
      entryReport := st.machine.entryReport * entryReportBase + code
      entryReportWord0 := w0
      entryReportBelow0 := reportBelowPush st.machine.entryReportBelow0 st.machine.entryReportWord0
      entryReportWord1 := w1
      entryReportBelow1 := reportBelowPush st.machine.entryReportBelow1 st.machine.entryReportWord1
      entryReportWord2 := w2
      entryReportBelow2 := reportBelowPush st.machine.entryReportBelow2 st.machine.entryReportWord2
      entryReportWord3 := w3
      entryReportBelow3 := reportBelowPush st.machine.entryReportBelow3 st.machine.entryReportWord3
      entryReportWord4 := w4
      entryReportBelow4 := reportBelowPush st.machine.entryReportBelow4 st.machine.entryReportWord4 } }

/-- The code on top of the state's report word. -/
@[inline] def _root_.SeLe4n.Model.SystemState.entryReportCode (st : SystemState) : Nat :=
  st.machine.entryReport % entryReportBase

/-- **Pop** the state's report: the word and the stacks the push found. -/
@[noinline] def _root_.SeLe4n.Model.SystemState.popEntryReport (st : SystemState) : SystemState :=
  { st with machine := { st.machine with
      entryReport := st.machine.entryReport / entryReportBase
      entryReportWord0 := reportBelowTop st.machine.entryReportBelow0
      entryReportBelow0 := reportStackPop st.machine.entryReportBelow0
      entryReportWord1 := reportBelowTop st.machine.entryReportBelow1
      entryReportBelow1 := reportStackPop st.machine.entryReportBelow1
      entryReportWord2 := reportBelowTop st.machine.entryReportBelow2
      entryReportBelow2 := reportStackPop st.machine.entryReportBelow2
      entryReportWord3 := reportBelowTop st.machine.entryReportBelow3
      entryReportBelow3 := reportStackPop st.machine.entryReportBelow3
      entryReportWord4 := reportBelowTop st.machine.entryReportBelow4
      entryReportBelow4 := reportStackPop st.machine.entryReportBelow4 } }

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
    s.machine.entryReportWord0 = w0 ∧ s.machine.entryReportWord1 = w1 ∧
      s.machine.entryReportWord2 = w2 ∧ s.machine.entryReportWord3 = w3 ∧
      s.machine.entryReportWord4 = w4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **A push followed by its pop is the identity**, on every state. -/
theorem _root_.SeLe4n.Model.SystemState.popEntryReport_pushEntryReport {code : Nat}
    {w0 w1 w2 w3 w4 : UInt64} (st : SystemState) (h : code < entryReportBase) :
    (st.pushEntryReport code w0 w1 w2 w3 w4).popEntryReport = st := by
  have hb : 0 < entryReportBase := by decide
  have hq : (st.machine.entryReport * entryReportBase + code) / entryReportBase =
      st.machine.entryReport := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt h, Nat.zero_add]
  simp only [SystemState.popEntryReport, SystemState.pushEntryReport, hq, reportStackPop_push,
    reportBelowTop_push]

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

/-- **The third continuation on a resolver's failure words**: the failed
lookup the words `t a b c` name (`LookupFault.ofWords`), pushed under kind `2`
as its canonical payload words, computed on the words, so no fault and no
error is built (`entryReportLookupW_eq`). -/
@[inline] def entryReportLookupW (t a b c : UInt64) (s : SystemState) : SystemState :=
  s.pushEntryReport (entryReportError 2 (.failedLookup false .invalidRoot)) 0
    (LookupFault.wordOfWords t a b c 0) (LookupFault.wordOfWords t a b c 1)
    (LookupFault.wordOfWords t a b c 2) (LookupFault.wordOfWords t a b c 3)

theorem entryReportLookupW_eq (t a b c : UInt64) (s : SystemState) :
    entryReportLookupW t a b c s =
      entryReportLookup (.failedLookup false (LookupFault.ofWords t a b c)) s := by
  simp only [entryReportLookupW, entryReportLookup, entryReportPushError, entryReportError,
    KernelError.payloadWord, LookupFault.word_ofWords]
  rfl

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
    (kLook : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (s : SystemState) : β :=
  let c := s.entryReportCode
  let w0 := s.machine.entryReportWord0
  let w1 := s.machine.entryReportWord1
  let w2 := s.machine.entryReportWord2
  let w3 := s.machine.entryReportWord3
  let w4 := s.machine.entryReportWord4
  let s' := s.popEntryReport
  if c < 4 then
    if c = 1 then kResOk s' else kGenOk s'
  else
    let d := c / 4 - 1
    if c % 4 = 0 then kGenErr d w0 w1 w2 w3 w4 s'
    else if c % 4 = 1 then kResErr d w0 w1 w2 w3 w4 s'
    else kLook d w0 w1 w2 w3 w4 s'

/-- **The report, handed on**: `entryReportOutcomeW` into continuations on
results, each refusal rebuilt from its words. -/
@[inline] def entryReportOutcome {β : Type}
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : KernelError → SystemState → β) (s : SystemState) : β :=
  entryReportOutcomeW (fun s => kGen (.ok ((), s))) (fun s => kRes (.ok ((), s)))
    (fun d w0 w1 w2 w3 w4 s => kGen (.error (KernelError.ofPayloadWords d w0 w1 w2 w3 w4, s)))
    (fun d w0 w1 w2 w3 w4 s => kRes (.error (KernelError.ofPayloadWords d w0 w1 w2 w3 w4, s)))
    (fun d w0 w1 w2 w3 w4 s => kLook (KernelError.ofPayloadWords d w0 w1 w2 w3 w4) s) s

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
    (kLook : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β) (kind : Nat) (hk : kind < 4)
    (e : KernelError)
    (s : SystemState) :
    entryReportOutcomeW kGenOk kResOk kGenErr kResErr kLook (entryReportPushError kind e s) =
      (if kind = 0 then kGenErr e.toDiscriminant (e.payloadWord 0) (e.payloadWord 1)
          (e.payloadWord 2) (e.payloadWord 3) (e.payloadWord 4) s
       else if kind = 1 then kResErr e.toDiscriminant (e.payloadWord 0) (e.payloadWord 1)
          (e.payloadWord 2) (e.payloadWord 3) (e.payloadWord 4) s
       else kLook e.toDiscriminant (e.payloadWord 0) (e.payloadWord 1) (e.payloadWord 2)
          (e.payloadWord 3) (e.payloadWord 4) s) := by
  obtain ⟨h1, h2, h3⟩ := entryReportError_div kind hk e
  have hl := entryReportError_lt hk e
  obtain ⟨hw0, hw1, hw2, hw3, hw4⟩ :=
    s.entryReportWords_pushEntryReport (code := entryReportError kind e) (w0 := e.payloadWord 0)
      (w1 := e.payloadWord 1) (w2 := e.payloadWord 2) (w3 := e.payloadWord 3)
      (w4 := e.payloadWord 4)
  simp only [entryReportOutcomeW, entryReportPushError, s.entryReportCode_pushEntryReport hl,
    s.popEntryReport_pushEntryReport hl, h1, h2, h3, hw0, hw1, hw2, hw3, hw4, if_false]

theorem entryReportOutcomeW_general {β : Type} (kGenOk kResOk : SystemState → β)
    (kGenErr kResErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (kLook : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
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
    (kLook : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
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
    (kLook : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β) (e : KernelError)
    (s : SystemState) :
    entryReportOutcomeW kGenOk kResOk kGenErr kResErr kLook (entryReportLookup e s) =
      kLook e.toDiscriminant (e.payloadWord 0) (e.payloadWord 1) (e.payloadWord 2)
        (e.payloadWord 3) (e.payloadWord 4) s := by
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
  rw [entryReportOutcomeW_lookup, KernelError.ofPayloadWords_payloadWord]

/-- Push a refusal for continuation `kind` given as its discriminant `d` and
payload words, as `entryReportPushError` pushes an error with those words. -/
@[inline] def entryReportPushErrorW (kind d : Nat) (w0 w1 w2 w3 w4 : UInt64)
    (s : SystemState) : SystemState :=
  s.pushEntryReport (kind + 4 * (d + 1)) w0 w1 w2 w3 w4

/-- An operand arm's result, its halves pushed as words, is `entryReportResolved`. -/
theorem liftReport_entryReportResolved :
    liftReport (entryReportPushOk 1) (entryReportPushErrorW 1) = entryReportResolved := by
  funext r
  rcases r with ⟨e, s⟩ | ⟨⟨⟩, s⟩ <;> rfl

/-- **`noCapRefusal` into a continuation on words** (D2b): the arm's refusal
taken apart, each error with a payload down to its words, and handed to `kErr`
as its discriminant and payload words, so a compiled arm whose refusal sites
build an error with a payload hands those words on and builds nothing: the join
point the arm's refusals meet at is specialised per constructor, its fields its
parameters.  Each payload constructor's words are written out, so no two
alternatives are the same code (`noCapRefusalW_eq`). -/
@[inline] def noCapRefusalW {β : Type} (noCap : Bool) (kOk : SystemState → β)
    (kErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) : β :=
  match r with
  | .ok ((), s) => kOk s
  | .error (e, s) =>
    match e with
    | .invalidCapability n =>
      if noCap = true ∧ n = 0 then onLookup (.invalidCapability 0) s
      else kErr (KernelError.invalidCapability 0).toDiscriminant n 0 0 0 0 s
    | .invalidArgument n => kErr (KernelError.invalidArgument 0).toDiscriminant n 0 0 0 0 s
    | .rangeError a b => kErr (KernelError.rangeError 0 0).toDiscriminant a b 0 0 0 s
    | .untypedRegionExhausted m =>
      kErr (KernelError.untypedRegionExhausted 0).toDiscriminant m 0 0 0 0 s
    | .failedLookup w .invalidRoot =>
      kErr (KernelError.failedLookup false .invalidRoot).toDiscriminant (if w then 1 else 0)
        1 0 0 0 s
    | .failedLookup w (.missingCapability l) =>
      kErr (KernelError.failedLookup false .invalidRoot).toDiscriminant (if w then 1 else 0)
        2 l.toUInt64 0 0 s
    | .failedLookup w (.depthMismatch l f) =>
      kErr (KernelError.failedLookup false .invalidRoot).toDiscriminant (if w then 1 else 0)
        3 l.toUInt64 f.toUInt64 0 s
    | .failedLookup w (.guardMismatch l g f) =>
      kErr (KernelError.failedLookup false .invalidRoot).toDiscriminant (if w then 1 else 0)
        4 l.toUInt64 g f.toUInt64 s
    | e => kErr e.toDiscriminant (e.payloadWord 0) (e.payloadWord 1) (e.payloadWord 2)
        (e.payloadWord 3) (e.payloadWord 4) s

theorem noCapRefusalW_eq {β : Type} (noCap : Bool) (kOk : SystemState → β)
    (kErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) :
    noCapRefusalW noCap kOk kErr onLookup r =
      noCapRefusal noCap (liftReport kOk kErr) onLookup r := by
  unfold noCapRefusal
  rcases r with ⟨e, s⟩ | ⟨⟨⟩, s⟩
  · cases e with
    | invalidCapability n =>
      by_cases h : noCap = true ∧ n = 0
      · obtain ⟨h1, rfl⟩ := h
        simp [noCapRefusalW, h1]
      · have h' : ¬ (noCap = true ∧ KernelError.invalidCapability n = .invalidCapability 0) := by
          simpa using h
        simp only [noCapRefusalW, if_neg h, if_neg h', liftReport]
        rfl
    | failedLookup w f =>
      cases f <;> (simp only [noCapRefusalW, liftReport, reduceCtorEq, and_false, if_false]; rfl)
    | _ => simp only [noCapRefusalW, liftReport, reduceCtorEq, and_false, if_false] <;> rfl
  · rfl

/-- **`dispatchOperandCheckedK`, its arm's result handed on as words**: the
arm's committed state to `kArmOk` and its refusal, as its discriminant and
payload words, to `kArmErr` (`noCapRefusalW`), so a refusal with a payload
reaches the report as scalars (`dispatchOperandCheckedKW_eq`). -/
@[inline] def dispatchOperandCheckedKW {β : Type} (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kArmOk : SystemState → β)
    (kArmErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (onLookupW : UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β) : β :=
  if !(st.scheduler.currentOnCore executingCore).isEqSome tid then
    kPre (.error (.illegalState, st))
  else
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    lookupSlotK tcb capAddr st
      (fun t a b c => onLookupW t a b c st)
      (fun cnode slot =>
        let c := SystemState.lookupSlotCap st { cnode := cnode, slot := slot }
        if slotEmpty c then onLookup (.invalidCapability 0) st
        else
          let k := fun noCap => noCapRefusalW noCap kArmOk kArmErr onLookup (arm c st)
          if receiveRefusedAt sid st c then k true else k (capHeldNone c))
  | some _ => kPre (.error (.illegalState, st))
  | none => kPre (.error (.objectNotFound, st))

theorem dispatchOperandCheckedKW_eq {β : Type} (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kArmOk : SystemState → β)
    (kArmErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (onLookupW : UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (hW : ∀ t a b c s, onLookupW t a b c s =
      onLookup (.failedLookup false (LookupFault.ofWords t a b c)) s) :
    dispatchOperandCheckedKW sid capAddr tid executingCore arm st kPre kArmOk kArmErr onLookup
        onLookupW =
      dispatchOperandCheckedK sid capAddr tid executingCore arm st kPre
        (liftReport kArmOk kArmErr) onLookup := by
  unfold dispatchOperandCheckedKW dispatchOperandCheckedK
  simp only [noCapRefusalW_eq, hW]
  rfl

/-- `dispatchOperandFilledK` with its arm's result handed on as words
(`dispatchOperandCheckedKW`): a refusal's words reach `kArmErr` with the TLB the
entry held handed back. -/
@[inline] def dispatchOperandFilledKW {β : Type} (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (held : Bool) (n0 : Nat)
    (stF : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kArmOk : SystemState → β)
    (kArmErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (onLookupW : UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β) : β :=
  dispatchOperandCheckedKW sid capAddr tid executingCore arm stF
    (undoFillRefusalK held executingCore n0 kPre) kArmOk
    (fun d w0 w1 w2 w3 w4 s => kArmErr d w0 w1 w2 w3 w4
      (if held then s else SeLe4n.Kernel.Architecture.tlbUndoFillOnCore s executingCore n0))
    (fun e s => onLookup e
      (if held then s else SeLe4n.Kernel.Architecture.tlbUndoFillOnCore s executingCore n0))
    (fun t a b c s => onLookupW t a b c
      (if held then s else SeLe4n.Kernel.Architecture.tlbUndoFillOnCore s executingCore n0))

theorem dispatchOperandFilledKW_eq {β : Type} (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (held : Bool) (n0 : Nat)
    (stF : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kArmOk : SystemState → β)
    (kArmErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (onLookupW : UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (hW : ∀ t a b c s, onLookupW t a b c s =
      onLookup (.failedLookup false (LookupFault.ofWords t a b c)) s) :
    dispatchOperandFilledKW sid capAddr tid executingCore arm held n0 stF kPre kArmOk kArmErr
        onLookup onLookupW =
      dispatchOperandFilledK sid capAddr tid executingCore arm held n0 stF kPre
        (liftReport kArmOk kArmErr) onLookup := by
  unfold dispatchOperandFilledKW dispatchOperandFilledK
  rw [dispatchOperandCheckedKW_eq _ _ _ _ _ _ _ _ _
    (fun e s => onLookup e
      (if held then s else SeLe4n.Kernel.Architecture.tlbUndoFillOnCore s executingCore n0))
    (fun t a b c s => onLookupW t a b c
      (if held then s else SeLe4n.Kernel.Architecture.tlbUndoFillOnCore s executingCore n0))
    (fun t a b c s => hW t a b c _)]
  congr 1
  funext r
  rcases r with ⟨e, s⟩ | ⟨⟨⟩, s⟩ <;> rfl

/-- `longOperandK` with its arm's result handed on as words. -/
@[inline] def longOperandKW {β : Type} (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (n : Nat) (st : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kArmOk : SystemState → β)
    (kArmErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (onLookupW : UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β) : β :=
  let held := SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid n
  let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
  dispatchOperandFilledKW sid capAddr tid executingCore arm held n0
    (if held then st else SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid n)
    kPre kArmOk kArmErr onLookup onLookupW

theorem longOperandKW_eq {β : Type} (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (n : Nat) (st : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kArmOk : SystemState → β)
    (kArmErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (onLookupW : UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (hW : ∀ t a b c s, onLookupW t a b c s =
      onLookup (.failedLookup false (LookupFault.ofWords t a b c)) s) :
    longOperandKW sid capAddr tid executingCore arm n st kPre kArmOk kArmErr onLookup onLookupW =
      longOperandK sid capAddr tid executingCore arm n st kPre (liftReport kArmOk kArmErr)
        onLookup := by
  unfold longOperandKW longOperandK
  exact dispatchOperandFilledKW_eq _ _ _ _ _ _ _ _ _ _ _ _ _ hW

/-- `overflowOneOperandK` with its arm's result handed on as words. -/
@[inline] def overflowOneOperandKW {β : Type} (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kArmOk : SystemState → β)
    (kArmErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (onLookupW : UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β) : β :=
  let held := SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid
  let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
  dispatchOperandFilledKW sid capAddr tid executingCore arm held n0
    (if held then st else SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid 1)
    kPre kArmOk kArmErr onLookup onLookupW

theorem overflowOneOperandKW_eq {β : Type} (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kArmOk : SystemState → β)
    (kArmErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (onLookupW : UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (hW : ∀ t a b c s, onLookupW t a b c s =
      onLookup (.failedLookup false (LookupFault.ofWords t a b c)) s) :
    overflowOneOperandKW sid capAddr tid executingCore arm st kPre kArmOk kArmErr onLookup
        onLookupW =
      overflowOneOperandK sid capAddr tid executingCore arm st kPre (liftReport kArmOk kArmErr)
        onLookup := by
  unfold overflowOneOperandKW overflowOneOperandK
  exact dispatchOperandFilledKW_eq _ _ _ _ _ _ _ _ _ _ _ _ _ hW

/-- **The reporting operand dispatch is the specification's**: the KW forms
into the report continuations, a lookup failure pushed from its words
(`entryReportLookupW`), are the K forms into `entryReportResolved` and
`entryReportLookup`. -/
theorem dispatchOperandCheckedKW_report (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → SystemState) :
    dispatchOperandCheckedKW sid capAddr tid executingCore arm st kPre (entryReportPushOk 1)
        (entryReportPushErrorW 1) entryReportLookup entryReportLookupW =
      dispatchOperandCheckedK sid capAddr tid executingCore arm st kPre entryReportResolved
        entryReportLookup := by
  rw [dispatchOperandCheckedKW_eq _ _ _ _ _ _ _ _ _ _ _ entryReportLookupW_eq,
    liftReport_entryReportResolved]

theorem longOperandKW_report (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (n : Nat) (st : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → SystemState) :
    longOperandKW sid capAddr tid executingCore arm n st kPre (entryReportPushOk 1)
        (entryReportPushErrorW 1) entryReportLookup entryReportLookupW =
      longOperandK sid capAddr tid executingCore arm n st kPre entryReportResolved
        entryReportLookup := by
  rw [longOperandKW_eq _ _ _ _ _ _ _ _ _ _ _ _ entryReportLookupW_eq,
    liftReport_entryReportResolved]

theorem overflowOneOperandKW_report (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → SystemState) :
    overflowOneOperandKW sid capAddr tid executingCore arm st kPre (entryReportPushOk 1)
        (entryReportPushErrorW 1) entryReportLookup entryReportLookupW =
      overflowOneOperandK sid capAddr tid executingCore arm st kPre entryReportResolved
        entryReportLookup := by
  rw [overflowOneOperandKW_eq _ _ _ _ _ _ _ _ _ _ _ entryReportLookupW_eq,
    liftReport_entryReportResolved]

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
  · simp only [lookupSlotK_eq]
    split
    · rfl
    · split
      · rfl
      · split <;> (unfold noCapRefusal; split <;> (try split) <;> rfl)
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
