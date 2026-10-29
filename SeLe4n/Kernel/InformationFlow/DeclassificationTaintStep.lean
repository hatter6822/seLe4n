-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.TaintPropagation

/-!
# The declassifications' taint steps, fused

WS-ZA ZA5.12.  `applySyscallTaintAfter` is the specification's taint step: it
builds the syscall's plan, the origination tags of the events the commit
recorded (`originationTags`, over `recordedSince`) and the seeded source taint,
all as lists and maps.  This module gives the three syscalls that record or
read the trail — `.declassify`, `.declassifySignal` and the audit pair — the
step the compiled dispatcher runs instead: it walks the audit ring's new
window in place (`originateWindow`), seeds a flow source by folding the window's
tags into the source's words carried as scalars (`seedWordsFrom`), and joins
words at their slots (`joinTaintAt`), building no list and no `TaintWords`.

Each step is proven equal to `applySyscallTaintAfter` of the syscall's plan,
given source words that decode to the pre-state's taint at the plan's flow
sources (`declassifyTaintStep_eq`, `declassifySignalTaintStep_eq`,
`auditTaintStep_eq`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-! ## Where a signal's taint goes -/

/-- WS-ZA ZA2.4: **where a signal's taint goes**, read from the pre-state before
the arm: no object operand, or the object's `signalDelivery`.  Its constructors
without a thread are boxed scalars, so the common case builds nothing. -/
inductive SignalTaintCase where
  | noObject
  | stored
  | toWaiter (w : SeLe4n.ThreadId)
  | toBound (t : SeLe4n.ThreadId)

/-- WS-ZA ZA4.7: a taint case as one word, so the entry carries it across the
signal as a scalar: `0` no object, `1` stored, `2w+2` to waiter `w`, `2t+3` to
bound TCB `t`. -/
@[inline] def SignalTaintCase.code : SignalTaintCase → Nat
  | .noObject => 0
  | .stored => 1
  | .toWaiter w => 2 * w.val + 2
  | .toBound t => 2 * t.val + 3

/-- The taint case a word stands for; inverse of `SignalTaintCase.code`. -/
@[inline] def SignalTaintCase.ofCode : Nat → SignalTaintCase
  | 0 => .noObject
  | 1 => .stored
  | n + 2 => if n % 2 = 0 then .toWaiter ⟨n / 2⟩ else .toBound ⟨n / 2⟩

@[simp] theorem SignalTaintCase.ofCode_code (tc : SignalTaintCase) :
    SignalTaintCase.ofCode tc.code = tc := by
  cases tc with
  | noObject => rfl
  | stored => rfl
  | toWaiter w =>
    show (if (2 * w.val) % 2 = 0 then _ else _) = _
    simp only [Nat.mul_mod_right, ↓reduceIte, SignalTaintCase.toWaiter.injEq]
    cases w; simp
  | toBound t =>
    show (if (2 * t.val + 1) % 2 = 0 then _ else _) = _
    simp only [Nat.mul_add_mod, Nat.one_mod, Nat.one_ne_zero, ↓reduceIte,
      SignalTaintCase.toBound.injEq]
    cases t; simp only [SeLe4n.ThreadId.mk.injEq]; omega

/-- WS-ZA ZA2.4: the signal's taint case, from the capability it resolved. -/
@[inline] def signalTaintCaseOfCap (st : SystemState) (cap : Capability) : SignalTaintCase :=
  match cap.target with
  | .object nid =>
      match signalDelivery st nid with
      | .stored => .stored
      | .toWaiter w => .toWaiter w
      | .toBound t => .toBound t
  | _ => .noObject

/-- WS-ZA ZA2.4: the signal's taint case, from its resolved operand. -/
def signalTaintCaseOf (st : SystemState) (operand : Option Capability) : SignalTaintCase :=
  match operand with
  | some cap => signalTaintCaseOfCap st cap
  | none => .noObject

/-- WS-ZA ZA2.4: the object a capability names — the notification a signal or
a wait moves taint at, the target a declassification downgrades — `⟨0⟩` when it
names none, where every step reading it reads nothing there
(`signalTaintCaseOfCap` is `.noObject`, `declassifyBypassB` is `false`). -/
@[inline] def capObjectId (cap : Capability) : SeLe4n.ObjId :=
  match cap.target with
  | .object nid => nid
  | _ => ⟨0⟩

/-- WS-ZA ZA2.4: the object a resolved operand names (`capObjectId`). -/
@[inline] def operandObjectId (operand : Option Capability) : SeLe4n.ObjId :=
  match operand with
  | some cap => capObjectId cap
  | none => ⟨0⟩

/-! ## The ring's new window -/

/-- The `n` events of the ring from position `i`, in order — the window a commit
recorded, as the specification reads it (`AuditRing.entriesFrom`). -/
def AuditRing.window (r : AuditRing) (i n : Nat) : List DeclassificationEvent :=
  (List.range n).map fun j => r.entry (i + j)

@[simp] theorem AuditRing.window_zero (r : AuditRing) (i : Nat) : r.window i 0 = [] := rfl

theorem AuditRing.window_succ (r : AuditRing) (i n : Nat) :
    r.window i (n + 1) = r.entry i :: r.window (i + 1) n := by
  unfold AuditRing.window
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  congr 1
  omega

/-- How many events the ring's window holds past `preLength`, when the trail
was not drained since `preEpoch`; none otherwise. -/
@[inline] def recordedCount (preEpoch preLength : Nat) (post : SystemState) : Nat :=
  if preEpoch = post.declassificationAudit.epoch then
    post.declassificationAudit.length - preLength
  else 0

/-- The events a commit recorded are the ring's window past the pre-state's
length (`recordedSince`, as compiled through `recordedSince_eq_ring`). -/
theorem recordedSince_eq_window (preEpoch preLength : Nat) (post : SystemState) :
    recordedSince preEpoch preLength post =
      post.declassificationAudit.window preLength (recordedCount preEpoch preLength post) := by
  rw [recordedSince_eq_ring]
  unfold recordedSinceOfRing recordedCount
  split
  · rfl
  · rfl

/-! ## The origination pass -/

/-- **The final origination pass over the window**, walked in place: each of
the `n` events from position `i` tags its target, then its subject, with its
timestamp — unless its target is the one key the downgrade released nothing at
(`nrB`, `nrId`: the plan's `noRelease`), and skipping a key the commit cleared or
bypassed (`exB`, `exId`).  The singletons reach the join as scalars
(`TaintWords.singletonWordsFlat`). -/
def originateWindow (r : AuditRing) (nrB : Bool) (nrId : SeLe4n.ObjId) (exB : Bool)
    (exId : SeLe4n.ObjId) : Nat → Nat → SystemState → SystemState
  | _, 0, s => s
  | i, n + 1, s =>
    let e := r.entry i
    let s :=
      if nrB && e.targetObject == nrId then s
      else
        let s :=
          if exB && e.targetObject == exId then s
          else joinTaintAt s e.targetObject (TaintWords.singletonWordsFlat e.timestamp)
        if exB && e.sourceSubject == exId then s
        else joinTaintAt s e.sourceSubject (TaintWords.singletonWordsFlat e.timestamp)
    originateWindow r nrB nrId exB exId (i + 1) n s

/-- The specification's final pass: the origination tags of `events`, those
naming an excluded key dropped, each joined at its key. -/
def originationPass (noRelease excluded : List SeLe4n.ObjId)
    (events : List DeclassificationEvent) (s : SystemState) : SystemState :=
  ((originationTags noRelease events).filter (fun p => !excluded.contains p.1)).foldl
    (fun s p => joinTaintAt s p.1 (TaintWords.singletonWords p.2)) s

theorem originationPass_cons (noRelease excluded : List SeLe4n.ObjId)
    (e : DeclassificationEvent) (events : List DeclassificationEvent) (s : SystemState) :
    originationPass noRelease excluded (e :: events) s =
      originationPass noRelease excluded events
        (if noRelease.contains e.targetObject then s
         else
          let s :=
            if excluded.contains e.targetObject then s
            else joinTaintAt s e.targetObject (TaintWords.singletonWords e.timestamp)
          if excluded.contains e.sourceSubject then s
          else joinTaintAt s e.sourceSubject (TaintWords.singletonWords e.timestamp)) := by
  unfold originationPass originationTags
  rw [List.flatMap_cons, List.filter_append, List.foldl_append]
  congr 1
  by_cases hR : noRelease.contains e.targetObject = true
  · simp only [hR, ↓reduceIte, List.filter_nil, List.foldl_nil]
  · simp only [hR, Bool.false_eq_true, ↓reduceIte]
    simp only [List.filter]
    cases excluded.contains e.targetObject <;> cases excluded.contains e.sourceSubject <;>
      simp only [Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true,
        List.foldl_cons, List.foldl_nil]

/-- **The walk is the specification's pass**, given the scalars that stand for
the plan's `noRelease` (`hNr`) and its cleared-or-bypassed keys (`hEx`). -/
theorem originateWindow_eq (r : AuditRing) (nrB : Bool) (nrId : SeLe4n.ObjId) (exB : Bool)
    (exId : SeLe4n.ObjId) (noRelease excluded : List SeLe4n.ObjId)
    (hNr : ∀ x, noRelease.contains x = (nrB && x == nrId))
    (hEx : ∀ x, excluded.contains x = (exB && x == exId)) :
    ∀ (n i : Nat) (s : SystemState),
      originateWindow r nrB nrId exB exId i n s =
        originationPass noRelease excluded (r.window i n) s
  | 0, _, _ => rfl
  | n + 1, i, s => by
      rw [AuditRing.window_succ, originationPass_cons]
      unfold originateWindow
      simp only [hNr, hEx, TaintWords.singletonWordsFlat_eq]
      exact originateWindow_eq r nrB nrId exB exId noRelease excluded hNr hEx n (i + 1) _

/-! ## `.declassify`: origination alone -/

/-- Whether a `.declassify`'s operand names a target holding no tracked content
(`declassifyBypassedTarget`): the one key its downgrade releases nothing at. -/
@[inline] def declassifyBypassB (st : SystemState) (operand : Option Capability) : Bool :=
  match operand with
  | some cap =>
      match cap.target with
      | .object targetId => !declassifyTargetHoldsContent st targetId
      | _ => false
  | none => false

/-- The two scalars stand for the plan's `noRelease`. -/
theorem declassifyBypassedTargets_contains (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (h : decoded.syscallId = .declassify) (x : SeLe4n.ObjId) :
    (declassifyBypassedTargets st tid decoded).contains x =
      (declassifyBypassB st (syscallOperandCap? st tid decoded.capAddr) &&
        x == operandObjectId (syscallOperandCap? st tid decoded.capAddr)) := by
  unfold declassifyBypassedTargets
  rw [h]
  rcases syscallOperandCap? st tid decoded.capAddr with _ | ⟨target, _, _⟩
  · rfl
  · cases target with
    | object targetId =>
      simp only [declassifyBypassedTarget, declassifyBypassB, operandObjectId, capObjectId]
      by_cases hC : declassifyTargetHoldsContent st targetId = true
      · simp [hC]
      · simp only [hC, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
        simp only [List.contains_cons, List.contains_nil, Bool.or_false]
    | _ => rfl

/-- **The `.declassify`'s taint step, fused**: no flow and no clear, so the
step is the window's origination, skipping the target the downgrade released
nothing at (`declassifyTaintStep_eq`). -/
@[inline] def declassifyTaintStep (nrB : Bool) (nrId : SeLe4n.ObjId) (preEpoch preLength : Nat)
    (post : SystemState) : SystemState :=
  originateWindow post.declassificationAudit nrB nrId false ⟨0⟩ preLength
    (recordedCount preEpoch preLength post) post

theorem declassifyTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (h : decoded.syscallId = .declassify)
    (preEpoch preLength : Nat) (preTaint : TaintMap) (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength preTaint post =
      declassifyTaintStep (declassifyBypassB st (syscallOperandCap? st tid decoded.capAddr))
        (operandObjectId (syscallOperandCap? st tid decoded.capAddr)) preEpoch preLength post := by
  unfold declassifyTaintStep
  rw [originateWindow_eq _ _ _ _ _ (declassifyBypassedTargets st tid decoded) []
    (declassifyBypassedTargets_contains st tid decoded h) (fun _ => rfl),
    ← recordedSince_eq_window]
  simp only [applySyscallTaintAfter, syscallTaintPlan, contentFlowClass, h,
    syscallRecordsDeclassification, ↓reduceIte, applyTaintStep, List.foldl_nil, List.append_nil]
  rfl

/-! ## The audit pair: no step -/

/-- **The audit calls' taint step is the identity**: they move no content and
record no downgrade (a drain advances the epoch, which originates nothing). -/
theorem auditTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult)
    (h : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (preEpoch preLength : Nat) (preTaint : TaintMap) (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength preTaint post =
      post := by
  rcases h with h | h <;>
    simp only [applySyscallTaintAfter, syscallTaintPlan, contentFlowClass, h,
      syscallRecordsDeclassification, Bool.false_eq_true, ↓reduceIte, applyTaintStep,
      List.foldl_nil, List.filter_nil]

/-! ## The seed of a flow source -/

/-- **A flow source's seed, over words**: the source's words `w` joined with
the timestamp of each recorded event naming the source as its target, then as
its subject — the specification's seed (`applyOrigination` of the origination
tags) at that key, read through words (`decode_seedWords`). -/
def seedWords (k : SeLe4n.ObjId) (w : TaintWords) : List DeclassificationEvent → TaintWords
  | [] => w
  | e :: events =>
    let w := if e.targetObject == k then TaintWords.join w (TaintWords.singletonWords e.timestamp)
      else w
    let w := if e.sourceSubject == k then TaintWords.join w (TaintWords.singletonWords e.timestamp)
      else w
    seedWords k w events

/-- WS-ZA ZA5.12 (**the decode lemma of the seed**): words decoding to a map's
taint at a source seed to the specification's seeded taint there. -/
theorem decode_seedWords (k : SeLe4n.ObjId) :
    ∀ (events : List DeclassificationEvent) (w : TaintWords) (P : TaintMap),
      w.decode = P k →
        (seedWords k w events).decode = applyOrigination (originationTags [] events) P k
  | [], _, _, h => h
  | e :: events, w, P, h => by
      have hO : originationTags [] (e :: events) =
          (e.targetObject, e.timestamp) :: (e.sourceSubject, e.timestamp) ::
            originationTags [] events := by
        simp [originationTags]
      rw [hO]
      unfold applyOrigination
      rw [List.foldl_cons, List.foldl_cons]
      apply decode_seedWords k events
      have hJ : ∀ (v : TaintWords) (Q : TaintMap) (o : SeLe4n.ObjId) (t : Nat), v.decode = Q k →
          (if o == k then TaintWords.join v (TaintWords.singletonWords t) else v).decode =
            (Q.joinAt o (DeclassificationTaint.singleton t)) k := by
        intro v Q o t hv
        by_cases ho : o = k
        · subst ho
          simp only [beq_self_eq_true, ↓reduceIte, TaintWords.decode_join, hv,
            TaintMap.joinAt_self, TaintWords.singletonWords_eq, DeclassificationTaint.decode_toWords]
        · have hb : (o == k) = false := by simpa using ho
          rw [hb, TaintMap.joinAt_ne _ (Ne.symm ho)]
          simpa using hv
      exact hJ _ _ _ _ (hJ _ _ _ _ h)

/-- **The seed, compiled**: the fold over the ring's window from position `i`,
the words carried as ten scalars and handed to `cont` (`seedWordsFrom_eq`), so
the seed builds no `TaintWords` and no list. -/
@[specialize] def seedWordsFrom {α : Sort _} (r : AuditRing) (k : SeLe4n.ObjId)
    (cont : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      Nat → Bool → α) :
    Nat → Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      Nat → Bool → α
  | _, 0, a0, a1, a2, a3, a4, a5, a6, a7, ac, as => cont a0 a1 a2 a3 a4 a5 a6 a7 ac as
  | i, n + 1, a0, a1, a2, a3, a4, a5, a6, a7, ac, as =>
    let e := r.entry i
    let w : TaintWords := ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩
    let w := TaintWords.selectWords (e.targetObject == k)
      (TaintWords.join w (TaintWords.singletonWordsFlat e.timestamp)) w
    let w := TaintWords.selectWords (e.sourceSubject == k)
      (TaintWords.join w (TaintWords.singletonWordsFlat e.timestamp)) w
    seedWordsFrom r k cont (i + 1) n w.tag0 w.tag1 w.tag2 w.tag3 w.tag4 w.tag5 w.tag6 w.tag7
      w.count w.saturated

theorem seedWordsFrom_eq {α : Sort _} (r : AuditRing) (k : SeLe4n.ObjId)
    (cont : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      Nat → Bool → α) :
    ∀ (n i : Nat) (w : TaintWords),
      seedWordsFrom r k cont i n w.tag0 w.tag1 w.tag2 w.tag3 w.tag4 w.tag5 w.tag6 w.tag7
          w.count w.saturated =
        let v := seedWords k w (r.window i n)
        cont v.tag0 v.tag1 v.tag2 v.tag3 v.tag4 v.tag5 v.tag6 v.tag7 v.count v.saturated
  | 0, _, _ => rfl
  | n + 1, i, w => by
      rw [AuditRing.window_succ]
      unfold seedWordsFrom
      simp only [TaintWords.selectWords_eq, TaintWords.singletonWordsFlat_eq,
        TaintWords.mk_fields]
      exact seedWordsFrom_eq r k cont n (i + 1) _

/-! ## `.declassifySignal`: a signal's flows, seeded, then origination -/

/-- **The declassified signal's taint step, fused.**  A signal's flows and clear
(`signalTaintCaseOfCap`), each source seeded with the window's tags at it
(`seedWordsFrom`, from the caller's words `wT` and the notification's words `wN`
captured before the arm), then the window's origination, skipping the
notification the delivery cleared or bypassed (`declassifySignalTaintStep_eq`).
Its plan releases at every target (`declassifyBypassedTargets` is empty), so no
event is dropped as a whole. -/
@[inline] def declassifySignalTaintStep (tc : SignalTaintCase) (nid : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (wT wN : TaintWords) (preEpoch preLength : Nat)
    (post : SystemState) : SystemState :=
  let r := post.declassificationAudit
  let n := recordedCount preEpoch preLength post
  seedWordsFrom r tid.toObjId (fun t0 t1 t2 t3 t4 t5 t6 t7 tn ts =>
    seedWordsFrom r nid (fun m0 m1 m2 m3 m4 m5 m6 m7 mn ms =>
      let sT : TaintWords := ⟨t0, t1, t2, t3, t4, t5, t6, t7, tn, ts⟩
      let sN : TaintWords := ⟨m0, m1, m2, m3, m4, m5, m6, m7, mn, ms⟩
      match tc with
      | .noObject => originateWindow r false ⟨0⟩ false ⟨0⟩ preLength n post
      | .stored => originateWindow r false ⟨0⟩ false ⟨0⟩ preLength n (joinTaintAt post nid sT)
      | .toWaiter w =>
          originateWindow r false ⟨0⟩ true nid preLength n
            (clearTaintAt (joinTaintAt (joinTaintAt post w.toObjId sT) w.toObjId sN) nid)
      | .toBound t =>
          originateWindow r false ⟨0⟩ true nid preLength n (joinTaintAt post t.toObjId sT))
      preLength n wN.tag0 wN.tag1 wN.tag2 wN.tag3 wN.tag4 wN.tag5 wN.tag6 wN.tag7 wN.count
      wN.saturated)
    preLength n wT.tag0 wT.tag1 wT.tag2 wT.tag3 wT.tag4 wT.tag5 wT.tag6 wT.tag7 wT.count
    wT.saturated

/-- The declassified signal's taint step is the specification's, given source
words that decode to the source taint at the caller (`hT`) and at the
notification its operand names (`hN`). -/
theorem declassifySignalTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (h : decoded.syscallId = .declassifySignal)
    (preEpoch preLength : Nat) (P : TaintMap) (wT wN : TaintWords)
    (hT : wT.decode = P tid.toObjId)
    (hN : wN.decode = P (operandObjectId (syscallOperandCap? st tid decoded.capAddr)))
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength P post =
      declassifySignalTaintStep (signalTaintCaseOf st (syscallOperandCap? st tid decoded.capAddr))
        (operandObjectId (syscallOperandCap? st tid decoded.capAddr)) tid wT wN preEpoch preLength
        post := by
  have hST := decode_seedWords tid.toObjId
    (post.declassificationAudit.window preLength (recordedCount preEpoch preLength post)) wT P hT
  unfold declassifySignalTaintStep
  rw [seedWordsFrom_eq, seedWordsFrom_eq]
  simp only [TaintWords.mk_fields]
  simp only [applySyscallTaintAfter, syscallTaintPlan, contentFlowClass, h,
    syscallRecordsDeclassification, ↓reduceIte, applyTaintStep, recordedSince_eq_window,
    contentFlowEdges, contentFlowClears, contentFlowBypassed]
  revert hN
  generalize syscallOperandCap? st tid decoded.capAddr = operand
  intro hN
  have hSN := decode_seedWords _
    (post.declassificationAudit.window preLength (recordedCount preEpoch preLength post)) wN P hN
  rcases operand with _ | ⟨target, _, _⟩
  · simp only [List.foldl_nil, List.append_nil, signalTaintCaseOf]
    exact (originateWindow_eq _ _ _ _ _ [] [] (fun _ => rfl) (fun _ => rfl) _ _ _).symm
  · cases target with
    | object nid =>
      simp only [operandObjectId, capObjectId] at hSN
      simp only [signalTaintCaseOf, signalTaintCaseOfCap, operandObjectId, capObjectId,
        signalTaintEdges, signalClearedNotification, signalBypassedNotification]
      cases signalDelivery st nid with
      | stored =>
        simp only [List.foldl_cons, List.foldl_nil, List.append_nil,
          joinTaintAt_toWords_of_decode _ _ hST]
        exact (originateWindow_eq _ _ _ _ _ [] [] (fun _ => rfl) (fun _ => rfl) _ _ _).symm
      | toWaiter w =>
        simp only [List.foldl_cons, List.foldl_nil, List.append_nil,
          joinTaintAt_toWords_of_decode _ _ hST, joinTaintAt_toWords_of_decode _ _ hSN]
        exact (originateWindow_eq _ _ _ _ _ [] [nid] (fun _ => rfl)
          (fun x => by rw [List.contains_cons, List.contains_nil, Bool.or_false, Bool.true_and])
          _ _ _).symm
      | toBound t =>
        simp only [List.foldl_cons, List.foldl_nil, List.nil_append,
          joinTaintAt_toWords_of_decode _ _ hST]
        exact (originateWindow_eq _ _ _ _ _ [] [nid] (fun _ => rfl)
          (fun x => by rw [List.contains_cons, List.contains_nil, Bool.or_false, Bool.true_and])
          _ _ _).symm
    | _ =>
      simp only [List.foldl_nil, List.append_nil, signalTaintCaseOf, signalTaintCaseOfCap]
      exact (originateWindow_eq _ _ _ _ _ [] [] (fun _ => rfl) (fun _ => rfl) _ _ _).symm

end SeLe4n.Kernel
