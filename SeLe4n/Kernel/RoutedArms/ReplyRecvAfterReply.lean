-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Report

/-!
# The routed reply-receive, its receive capability read after the reply

seL4's `SysReplyRecv` runs `handleInvocation` on the reply capability before
`handleRecv` looks the receive capability up.  Where the reply answers a caller
and the entry refuses the receive capability (`replyRecvRefusedOnEntry?`), the
routed entry runs the reply step and reads the receive capability on the state
it left (`replyRecvRoutedK`, the specification).

Compiled, the question is asked only where the entry's operand route refuses
the receive capability with nothing written, on the state it was handed: its
lookup's failure, an empty slot, a receive capability of the wrong type or
without its right, and an endpoint whose flow gate refuses the receive
(`replyRecvOperandCheckedKW`).  The flow gate reads only the labelling context
and the capability, so it is tested before the arm.  The route that commits a
receive asks nothing, and a refusal the arm returns is handed on untested.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Whether a resolved slot's capability names no endpoint the receive's flow
gate admits: an endpoint whose gate refuses the receiver, or a target that is
no endpoint.  Out of line, with the slot borrowed, as `receiveSlotRefused`. -/
@[noinline] def receiveSlotEndpointRefused (ctx : @& LabelingContext) (tid : SeLe4n.ThreadId)
    (c : @& Option Capability) : Bool :=
  match c with
  | some cap =>
    match cap.target with
    | .object epId => !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid)
    | _ => true
  | none => false

/-- **Whether a reply-receive's reply answers a caller**, on the state it is
handed (`replyRecvAnsweringReply?`), in continuation form: no extra capability
of the reply fails, the reply capability at `replyWord` resolves to a reply
object whose caller the reply answers.  Out of line, with the state borrowed,
so nothing is built and the state is not held. -/
@[noinline] def replyRecvAnswersOn (ctx : @& LabelingContext) (tid : SeLe4n.ThreadId)
    (replyWord : UInt64) (extraCaps : Nat) (st : @& SystemState) : Bool :=
  callerExtraCapsFailK st tid extraCaps (fun _ => false) fun _ =>
    resolveReplyRecvK st tid (SeLe4n.CPtr.ofWord replyWord)
      (fun c => replyRecvReplyAnswers ctx st tid c) (fun _ => false) (fun _ => false)
      (fun _ _ _ _ _ => true)

/-- **The reply-receive's operand route, its refusals asked whether the reply
answers first**: `dispatchOperandCheckedKW` on `.replyRecv`, its arm and the
telling apart of its result in one continuation (`armK`, run once, handed
whether the gate refused the capability, as `noCapRefusalW` is handed it),
where each refusal of the receive capability that writes nothing -- the
operand's failed lookup, an empty slot, a capability of the wrong type or
without its right (the arm's refusal on the state it was handed), and an
endpoint whose flow gate refuses the receive, tested before the arm -- first
asks `answers` of the state it was handed, and runs `after` on it where the
reply answers.  The route that commits asks nothing, and every refusal the arm
returns past those is handed to `kArmErr` untested. -/
@[inline] def replyRecvOperandCheckedKW {β : Type} (ctx : LabelingContext)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (xc : Nat)
    (armK : Option Capability → SystemState → Bool → β)
    (st : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kArmOk : SystemState → β)
    (kArmErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (onLookupAtW : SeLe4n.CPtr → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (answers : SystemState → Bool) (after : SystemState → β) : β :=
  if !(st.scheduler.currentOnCore executingCore).isEqSome tid then
    kPre (.error (.illegalState, st))
  else
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    lookupSlotK tcb capAddr st
      (fun t a b c => if answers st then after st else onLookupAtW capAddr t a b c st)
      (fun cnode slot =>
        let c := SystemState.lookupSlotCap st { cnode := cnode, slot := slot }
        extraCapsLookupK st tcb xc (fun cptr t a b c' => onLookupAtW cptr t a b c' st)
          (fun _ =>
            if slotHeldNone c then
              if answers st then after st else onLookup (.invalidCapability 0) st
            else
              let refused := receiveRefusedAt .replyRecv tid st c
              if !refused && receiveSlotEndpointRefused ctx tid c && answers st then after st
              else armK c st refused))
  | some _ => kPre (.error (.illegalState, st))
  | none => kPre (.error (.objectNotFound, st))

/-- `replyRecvAfterReplyOutcome` with its one question of the entry state --
whether the operand's lookup passed there -- asked before the route runs
(`entryLookupOk`), so the route is handed the state with nothing else holding
it (`replyRecvAfterReplyOutcome_eq_of`). -/
@[inline] def replyRecvAfterReplyOutcomeOf {β : Type} (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (gate : SyscallGate) (entryLookupOk : Bool)
    (kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SeLe4n.CPtr → KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) : β :=
  match r with
  | .ok v => kRes (.ok v)
  | .error (ke, s) =>
    let replyFault := fun (_ : Unit) =>
      match receiveReplyFaults { gate with cspaceRootCap := callerCspaceRoot s tid } decoded s ke with
      | some (replyAddr, lf) => kLook replyAddr (.failedLookup false lf) s
      | none => kRes (.error (ke, s))
    if entryLookupOk then replyFault ()
    else
      match syscallOperandLookup decoded.syscallId gate
          (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) s with
      | .error (a, e) => if e = ke then kLook a e s else replyFault ()
      | .ok _ => replyFault ()

/-- Whether the operand's lookup passes on a state, as a word. -/
@[inline] def replyRecvEntryLookupOk (decoded : SyscallDecodeResult) (gate : SyscallGate)
    (st : SystemState) : Bool :=
  match syscallOperandLookup decoded.syscallId gate
      (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) st with
  | .ok _ => true
  | .error _ => false

theorem replyRecvAfterReplyOutcome_eq_of {β : Type} (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (gate : SyscallGate) (st : SystemState)
    (kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SeLe4n.CPtr → KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) :
    replyRecvAfterReplyOutcome tid decoded gate st kRes kLook r =
      replyRecvAfterReplyOutcomeOf tid decoded gate (replyRecvEntryLookupOk decoded gate st)
        kRes kLook r := by
  unfold replyRecvAfterReplyOutcome replyRecvAfterReplyOutcomeOf replyRecvEntryLookupOk
  rcases r with ⟨ke, s⟩ | v
  · dsimp only
    cases syscallOperandLookup decoded.syscallId gate
        (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) st <;> rfl
  · rfl

/-- **The after-reply route, compiled**: `replyRecvRoutedK` with the questions
it asks of the entry state -- the reply it answers and the operand's lookup --
asked before the reply step, then the one compiled after-reply route
(`replyRecvAfterReplyRunR`), whose taint step runs on words captured as
scalars; `k` where the route does not run (`replyRecvAfterReplyRoutedOn_eq`). -/
@[inline] def replyRecvAfterReplyRoutedOn {β : Type} (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) (kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SeLe4n.CPtr → KernelError → SystemState → β) (k : Unit → β) : β :=
  match replyRecvRefusedOnEntry? ctx decoded tid st with
  | none => k ()
  | some (gate, rid, prevCaller, replyBadge, replyGrant) =>
    let entryLookupOk := replyRecvEntryLookupOk decoded gate st
    replyRecvAfterReplyOutcomeOf tid decoded gate entryLookupOk kRes kLook
      (if !(st.scheduler.currentOnCore executingCore).isEqSome tid then .error (.illegalState, st)
       else
        replyRecvAfterReplyRunR ctx gate decoded tid executingCore rid prevCaller replyBadge
          replyGrant st)

theorem replyRecvAfterReplyRoutedOn_eq {β : Type} (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) (kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SeLe4n.CPtr → KernelError → SystemState → β) (k : Unit → β) :
    replyRecvAfterReplyRoutedOn ctx decoded tid executingCore st kRes kLook k =
      replyRecvRoutedK ctx decoded tid executingCore st kRes kLook (k ()) := by
  unfold replyRecvAfterReplyRoutedOn replyRecvRoutedK
  cases hR : replyRecvRefusedOnEntry? ctx decoded tid st with
  | none => rfl
  | some q =>
    obtain ⟨gate, rid, prevCaller, replyBadge, replyGrant⟩ := q
    obtain ⟨tcb, -, hT, hG, hA, -⟩ := replyRecvRefusedOnEntry?_some hR
    dsimp only
    rw [replyRecvAfterReplyOutcome_eq_of]
    unfold replyRecvRoutedR
    rw [hR]
    dsimp only
    by_cases hC : (!(st.scheduler.currentOnCore executingCore).isEqSome tid) = true
    · rw [if_pos hC, if_pos hC]
    · rw [if_neg hC, if_neg hC]
      subst hG
      rw [replyRecvAfterReplyRunR_eq (replyRecvReplyLegEdges_of_answering hT hA)]
      cases replyRecvAnsweringThenR ctx (replyRecvReceiveEndpoint ctx
          (replyRecvCallerGate decoded tid tcb) tid) decoded tid executingCore rid prevCaller
          replyBadge replyGrant st with
      | error es => obtain ⟨e, s⟩ := es; rfl
      | ok p => obtain ⟨⟨⟩, stPost⟩ := p; rfl

/-- `replyRecvAnswersOn` is whether the reply answers (`replyRecvAnsweringReply?`)
through the caller's gate. -/
theorem replyRecvAnswersOn_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState) (replyWord : UInt64)
    (hT : st.getObject? tid.toObjId = some (.tcb tcb))
    (hW : decoded.replyCPtr = SeLe4n.CPtr.ofWord replyWord) :
    replyRecvAnswersOn ctx tid replyWord decoded.msgInfo.extraCaps st =
      (replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st).isSome := by
  unfold replyRecvAnswersOn replyRecvAnsweringReply?
  rw [callerExtraCapsFailK_eq]
  cases callerExtraCapsFault? st tid decoded.msgInfo.extraCaps with
  | some _ => rfl
  | none =>
    dsimp only
    rw [resolveReplyRecvK_eq_of st tid _ _ _ _ _ (fun _ _ _ _ => true) (fun _ _ _ _ _ _ => rfl),
      ← hW, resolveReplyRecvReplyR_eq st tid (replyRecvCallerGate decoded tid tcb) decoded rfl
        (by simp only [replyRecvCallerGate, callerCspaceRoot, hT])]
    cases resolveReplyRecvReply (replyRecvCallerGate decoded tid tcb) decoded st with
    | error e => rfl
    | ok r =>
      cases r with
      | none => rfl
      | some q =>
        obtain ⟨rid, c, b, g⟩ := q
        dsimp only
        cases replyRecvReplyAnswers ctx st tid c <;> rfl

theorem receiveBoundRefuses_replyRecv (tid : SeLe4n.ThreadId) (st : SystemState)
    (cap : Capability) : receiveBoundRefuses .replyRecv tid st cap = false := by
  unfold receiveBoundRefuses
  cases cap.target <;> rfl

/-- **The receive's endpoint on the caller's gate**, as the operand route reads
it: the operand's slot, its capability, the reserved-object check, the type, the
right, then the target and its flow gate. -/
theorem replyRecvReceiveEndpoint_callerGate (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState) :
    replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st =
      match lookupSlot tcb decoded.capAddr st with
      | .error f => .error (.failedLookup false f)
      | .ok ref =>
        match SystemState.lookupSlotCap st ref with
        | none => .error (.invalidCapability 0)
        | some cap =>
          if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0)
          else if !syscallTargetAccepted .replyRecv st cap then .error (.invalidCapability 0)
          else if !cap.hasRight (syscallRequiredRight decoded.syscallId) then
            .error (syscallMissingRightError .replyRecv)
          else
            match cap.target with
            | .object epId =>
              if endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
                .ok epId
              else .error .flowDenied
            | _ => .error (.invalidCapability 0) := by
  unfold replyRecvReceiveEndpoint syscallResolveCap replyRecvCallerGate
  simp only [SyscallGate.lookupSlot_mk]
  cases lookupSlot tcb decoded.capAddr st with
  | error f => rfl
  | ok ref =>
    dsimp only
    cases SystemState.lookupSlotCap st ref with
    | none => rfl
    | some cap =>
      dsimp only
      by_cases hR : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
      · rw [if_pos hR, if_pos hR]
      · rw [if_neg hR, if_neg hR]
        rfl

/-- Where the receive's endpoint is refused on the entry state, the after-reply
route runs exactly where the reply answers. -/
theorem replyRecvRefusedOnEntry?_isSome_of_refused {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {tcb : TCB} {st : SystemState}
    (hT : st.getObject? tid.toObjId = some (.tcb tcb)) {e : KernelError}
    (hE : replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st = .error e) :
    (replyRecvRefusedOnEntry? ctx decoded tid st).isSome =
      (replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st).isSome := by
  unfold replyRecvRefusedOnEntry?
  rw [hT]
  dsimp only
  cases replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st with
  | none => rfl
  | some q =>
    obtain ⟨rid, c, b, g⟩ := q
    dsimp only
    rw [hE]
    rfl

/-- Where the receive's endpoint passes on the entry state, the after-reply
route does not run. -/
theorem replyRecvRefusedOnEntry?_of_ok {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {tcb : TCB} {st : SystemState}
    (hT : st.getObject? tid.toObjId = some (.tcb tcb)) {ep : SeLe4n.ObjId}
    (hE : replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st = .ok ep) :
    replyRecvRefusedOnEntry? ctx decoded tid st = none := by
  unfold replyRecvRefusedOnEntry?
  rw [hT]
  dsimp only
  cases replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st with
  | none => rfl
  | some q =>
    obtain ⟨rid, c, b, g⟩ := q
    dsimp only
    rw [hE]

/-- **The reply-receive's operand route is the entry's, or the after-reply
route where it runs** (`replyRecvRefusedOnEntry?`): every refusal it asks at
refuses the receive's endpoint on the state it was handed, so the question it
asks there is whether the after-reply route runs; where it does, every path
reaches such a refusal, and where it does not, every question answers no. -/
theorem replyRecvOperandCheckedKW_eq {β : Type} (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (xc : Nat) (arm : Option Capability → RefusalCarrying Unit)
    (armK : Option Capability → SystemState → Bool → β)
    (st : SystemState)
    (kPre : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kArmOk : SystemState → β)
    (kArmErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β)
    (onLookupAtW : SeLe4n.CPtr → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (answers : SystemState → Bool) (after : SystemState → β) (tcb : TCB)
    (hArmK : armK = fun c s noCap => noCapRefusalW noCap kArmOk kArmErr
      (fun e s => if answers s then after s else onLookup e s) (arm c s))
    (hSid : decoded.syscallId = .replyRecv)
    (hT : st.getObject? tid.toObjId = some (.tcb tcb)) (hX : xc = 0)
    (hArm : ∀ cap, SeLe4n.Kernel.capTargetsReservedKernelObject cap = false →
      receiveGateRefuses .replyRecv tid st cap = true →
      arm (some cap) st = .error (.invalidCapability 0, st))
    (hAns : answers st =
      (replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st).isSome) :
    replyRecvOperandCheckedKW ctx decoded.capAddr tid executingCore xc armK st kPre kArmOk kArmErr
        onLookup onLookupAtW answers after =
      if (replyRecvRefusedOnEntry? ctx decoded tid st).isSome then
        (if (st.scheduler.currentOnCore executingCore).isEqSome tid then after st
         else kPre (.error (.illegalState, st)))
      else
        dispatchOperandCheckedKW .replyRecv decoded.capAddr tid executingCore xc arm st kPre
          kArmOk kArmErr onLookup onLookupAtW := by
  subst hX hArmK
  have hSite : ∀ e, replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st =
      .error e → answers st = (replyRecvRefusedOnEntry? ctx decoded tid st).isSome :=
    fun e hE => by rw [hAns, replyRecvRefusedOnEntry?_isSome_of_refused hT hE]
  have hE0 := replyRecvReceiveEndpoint_callerGate ctx decoded tid tcb st
  rw [hSid] at hE0
  unfold replyRecvOperandCheckedKW dispatchOperandCheckedKW
  cases hCur : (st.scheduler.currentOnCore executingCore).isEqSome tid
  · all_goals (cases (replyRecvRefusedOnEntry? ctx decoded tid st).isSome <;> rfl)
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hT, lookupSlotK_eq,
    extraCapsLookupK_eq, lookupExtraCaps_zero]
  cases hL : lookupSlot tcb decoded.capAddr st with
  | error f =>
    rw [hL] at hE0
    rw [hSite _ hE0]
    all_goals (cases (replyRecvRefusedOnEntry? ctx decoded tid st).isSome <;> rfl)
  | ok ref =>
    rw [hL] at hE0
    dsimp only at hE0 ⊢
    cases hS : SystemState.lookupSlotCap st ref with
    | none =>
      rw [hS] at hE0
      rw [hSite _ hE0]
      all_goals (cases (replyRecvRefusedOnEntry? ctx decoded tid st).isSome <;> rfl)
    | some cap =>
      rw [hS] at hE0
      dsimp only at hE0
      have hHeld : slotHeldNone (some cap) = SeLe4n.Kernel.capTargetsReservedKernelObject cap := rfl
      rw [hHeld]
      cases hRes : SeLe4n.Kernel.capTargetsReservedKernelObject cap
      · rw [hRes] at hE0
        simp only [Bool.false_eq_true, ↓reduceIte] at hE0 ⊢
        rw [receiveRefusedAt_some]
        cases hG : receiveGateRefuses .replyRecv tid st cap
        · simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
          unfold receiveGateRefuses at hG
          rw [receiveBoundRefuses_replyRecv] at hG
          have hAcc : syscallTargetAccepted .replyRecv st cap = true := by
            cases h : syscallTargetAccepted .replyRecv st cap
            · rw [h] at hG; cases hG
            · rfl
          have hRt : cap.hasRight (syscallRequiredRight .replyRecv) = true := by
            cases h : cap.hasRight (syscallRequiredRight .replyRecv)
            · rw [h, hAcc] at hG; cases hG
            · rfl
          rw [hAcc, hRt] at hE0
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hE0
          cases hF : receiveSlotEndpointRefused ctx tid (some cap)
          · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            unfold receiveSlotEndpointRefused at hF
            dsimp only at hF
            cases hTg : cap.target with
            | object epId =>
              rw [hTg] at hF hE0
              dsimp only at hF hE0
              have hFl : endpointFlowGate ctx epId (ctx.endpointLabelOf epId)
                  (ctx.threadLabelOf tid) = true := by
                cases h : endpointFlowGate ctx epId (ctx.endpointLabelOf epId)
                    (ctx.threadLabelOf tid)
                · rw [h] at hF; cases hF
                · rfl
              rw [hFl] at hE0
              simp only [↓reduceIte] at hE0
              rw [replyRecvRefusedOnEntry?_of_ok hT hE0]
              rfl
            | _ => all_goals (rw [hTg] at hF; cases hF)
          · simp only [Bool.true_and, ↓reduceIte]
            unfold receiveSlotEndpointRefused at hF
            dsimp only at hF
            have hEr : ∃ e, replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb)
                tid st = .error e := by
              rw [hE0]
              cases hTg : cap.target with
              | object epId =>
                rw [hTg] at hF
                dsimp only at hF ⊢
                rw [Bool.not_eq_true'] at hF
                rw [hF]
                exact ⟨_, rfl⟩
              | _ => exact ⟨_, rfl⟩
            obtain ⟨e, hEr⟩ := hEr
            rw [hSite _ hEr]
            all_goals (cases (replyRecvRefusedOnEntry? ctx decoded tid st).isSome <;> rfl)
        · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          rw [hArm cap hRes hG]
          unfold receiveGateRefuses at hG
          rw [receiveBoundRefuses_replyRecv, Bool.or_false] at hG
          have hEr : ∃ e, replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb)
              tid st = .error e := by
            rw [hE0]
            cases hAcc : syscallTargetAccepted .replyRecv st cap
            · exact ⟨_, rfl⟩
            · rw [hAcc] at hG
              cases hRt : cap.hasRight (syscallRequiredRight .replyRecv)
              · exact ⟨_, rfl⟩
              · rw [hRt] at hG; cases hG
          obtain ⟨e, hEr⟩ := hEr
          have hA := hSite _ hEr
          simp only [noCapRefusalW, and_self, ↓reduceIte]
          rw [hA]
          all_goals (cases (replyRecvRefusedOnEntry? ctx decoded tid st).isSome <;> rfl)
      · rw [hRes] at hE0
        simp only [↓reduceIte] at hE0
        rw [hSite _ hE0]
        all_goals (cases (replyRecvRefusedOnEntry? ctx decoded tid st).isSome <;> rfl)

/-- The reply-receive's arm refuses a capability of the wrong type or without
its right with `.invalidCapability 0` on the state it was handed. -/
theorem replyRecvOperandArmThenTaintR_gateRefused (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState) (hRes : SeLe4n.Kernel.capTargetsReservedKernelObject cap = false)
    (hG : receiveGateRefuses .replyRecv tid st cap = true) :
    replyRecvOperandArmThenTaintR ctx layout rf len extraCaps label tid executingCore
      (syscallRequiredRight .replyRecv) (some cap) st = .error (.invalidCapability 0, st) := by
  unfold receiveGateRefuses at hG
  rw [receiveBoundRefuses_replyRecv, Bool.or_false] at hG
  unfold replyRecvOperandArmThenTaintR
  dsimp only
  rw [hRes]
  cases hAcc : syscallTargetAccepted .replyRecv st cap
  · rfl
  · rw [hAcc] at hG
    cases hRt : cap.hasRight (syscallRequiredRight .replyRecv)
    · rfl
    · rw [hRt] at hG; cases hG

/-- The long reply-receive's arm refuses as the short one does. -/
theorem replyRecvLongOperandArmThenTaintR_gateRefused (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState) (hRes : SeLe4n.Kernel.capTargetsReservedKernelObject cap = false)
    (hG : receiveGateRefuses .replyRecv tid st cap = true) :
    replyRecvLongOperandArmThenTaintR ctx rf len extraCaps label tid executingCore
      (syscallRequiredRight .replyRecv) (some cap) st = .error (.invalidCapability 0, st) := by
  unfold receiveGateRefuses at hG
  rw [receiveBoundRefuses_replyRecv, Bool.or_false] at hG
  unfold replyRecvLongOperandArmThenTaintR
  dsimp only
  rw [hRes]
  cases hAcc : syscallTargetAccepted .replyRecv st cap
  · rfl
  · rw [hAcc] at hG
    cases hRt : cap.hasRight (syscallRequiredRight .replyRecv)
    · rfl
    · rw [hRt] at hG; cases hG

/-- **The after-reply route, out of line**: the decode the route reads built
from the routed operands and the message words `msgRegs`, the route run on the
state it is handed (`replyRecvAfterReplyRoutedOn`) and its result reported.
Called only where the entry's route refuses the receive capability with nothing
written and the reply answers. -/
@[noinline] def replyRecvAfterReplyRoutedArm (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (capWord : UInt64)
    (msgRegs : Array SeLe4n.RegValue) (len extraCaps label : Nat) (st : SystemState) :
    SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    replyRecvAfterReplyRoutedOn ctx
      (replyRecvRoutedDecode (SeLe4n.CPtr.ofWord capWord) msgRegs
        (replyRecvReplyAddr tcb.registerContext) len extraCaps label)
      tid executingCore st entryReportResolved entryReportLookupFor
      (fun _ => entryReportGeneral (.error (.illegalState, st)))
  | _ => entryReportGeneral (.error (.illegalState, st))

/-- **The reply-receive's operand arm in continuation form**: the slot check,
gate, checked arm `checked` and taint step of `replyRecvOperandArmThenTaintR`
(and its long form), a commit handed to `kOk` with its taint step applied, a
refusal before the arm to `kRefused` as its error and state, and a refusal of
the arm to `kStep` as its error and state with the words the entry route's
refusal step reads, captured before the arm
(`replyRecvOperandArmThenTaintKE_eq`).  No pair is built around a refusal.
Inlined as written into each routed arm that runs it, so it is no compiled
function of its own. -/
@[macro_inline] def replyRecvOperandArmThenTaintKE {β : Type} (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (extraCaps : Nat)
    (tid : SeLe4n.ThreadId) (requiredRight : AccessRight)
    (checked : Capability → RefusalCarrying Unit)
    (operand : Option Capability) (st : SystemState) (kOk : SystemState → β)
    (kRefused : KernelError → SystemState → β)
    (kStep : Nat → Nat → Bool → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → Nat → Bool → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → Nat → Bool → KernelError → SystemState → β) : β :=
  match operand with
  | none => kRefused (.invalidCapability 0) st
  | some cap =>
      if SeLe4n.Kernel.capTargetsReservedKernelObject cap then kRefused (.invalidCapability 0) st
      else if !syscallTargetAccepted .replyRecv st cap then kRefused (.invalidCapability 0) st
      else if cap.hasRight requiredRight then
        let signalCode := receiveTaintSignalCode st tid cap
        let sourceCode := receiveTaintSourceCode st cap
        let callerCode := replyRecvTaintCallerCode st tid layout rf extraCaps
        let answered := replyRecvAnsweringCallerCode ctx tid
          (SeLe4n.readRegWord rf layout.replyReg) extraCaps st
        let awaited := senderAwaitsReceiveOfCode st sourceCode
        withTaintWordsAt st (notifObjOfCode signalCode) fun n0 n1 n2 n3 n4 n5 n6 n7 nc ns =>
        withTaintWordsAt st (threadObjOfCode sourceCode) fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
        withTaintWordsAt st tid.toObjId fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
        match checked cap st with
        | .error (e, s) =>
            kStep answered sourceCode awaited b0 b1 b2 b3 b4 b5 b6 b7 bc bs
              a0 a1 a2 a3 a4 a5 a6 a7 ac as e s
        | .ok ((), stPost) =>
            kOk (replyRecvTaintStep signalCode sourceCode callerCode tid
              ⟨n0, n1, n2, n3, n4, n5, n6, n7, nc, ns⟩ ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩
              ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩ stPost)
      else kRefused (syscallMissingRightError .replyRecv) st

/-- **The continuation-form arm is the reply-receive's arm, its result told
apart**: a commit to `kOk`, a refusal to `kErr`, with the entry route's
refusal step applied to the state of a refusal of the checked arm, as
`replyRecvOperandArmThenTaintR` applies it.  Unconditional. -/
theorem replyRecvOperandArmThenTaintKE_eq {β : Type} (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) (st : SystemState) (kOk : SystemState → β)
    (kErr kRefused : KernelError → SystemState → β)
    (kStep : Nat → Nat → Bool → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → Nat → Bool → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → Nat → Bool → KernelError → SystemState → β)
    (hR : ∀ e s, kRefused e s = kErr e s)
    (hS : ∀ n c w b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as e s,
      kStep n c w b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as e s =
        kErr e (replyRecvEntryRefusalStepW n c w tid b0 b1 b2 b3 b4 b5 b6 b7 bc bs
          a0 a1 a2 a3 a4 a5 a6 a7 ac as s)) :
    replyRecvOperandArmThenTaintKE ctx layout rf extraCaps tid requiredRight
        (fun cap => endpointReplyRecvCheckedArmR ctx layout rf len extraCaps label tid
          executingCore cap) operand st kOk kRefused kStep =
      match replyRecvOperandArmThenTaintR ctx layout rf len extraCaps label tid executingCore
          requiredRight operand st with
      | .ok ((), s) => kOk s
      | .error (e, s) => kErr e s := by
  have hS' : (fun n c w b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as e s =>
      kErr e (replyRecvEntryRefusalStepW n c w tid b0 b1 b2 b3 b4 b5 b6 b7 bc bs
        a0 a1 a2 a3 a4 a5 a6 a7 ac as s)) = kStep := by
    funext n c w b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as e s
    exact (hS n c w b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as e s).symm
  have hR' : kErr = kRefused := funext fun e => funext fun s => (hR e s).symm
  subst hS' hR'
  unfold replyRecvOperandArmThenTaintKE replyRecvOperandArmThenTaintR
  cases operand with
  | none => rfl
  | some cap =>
    dsimp only
    cases SeLe4n.Kernel.capTargetsReservedKernelObject cap
    · cases syscallTargetAccepted .replyRecv st cap
      · rfl
      · cases cap.hasRight requiredRight
        · rfl
        · dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, withTaintWordsAt]
          cases endpointReplyRecvCheckedArmR ctx layout rf len extraCaps label tid executingCore
              cap st with
          | error p => obtain ⟨e, s⟩ := p; rfl
          | ok p => obtain ⟨⟨⟩, s⟩ := p; rfl
    · rfl

/-- The long continuation-form arm is the long arm, its result told apart, as
the short one's (`replyRecvOperandArmThenTaintKE_eq`).  Unconditional. -/
theorem replyRecvLongOperandArmThenTaintKE_eq {β : Type} (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) (st : SystemState) (kOk : SystemState → β)
    (kErr kRefused : KernelError → SystemState → β)
    (kStep : Nat → Nat → Bool → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → Nat → Bool → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → Nat → Bool → KernelError → SystemState → β)
    (hR : ∀ e s, kRefused e s = kErr e s)
    (hS : ∀ n c w b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as e s,
      kStep n c w b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as e s =
        kErr e (replyRecvEntryRefusalStepW n c w tid b0 b1 b2 b3 b4 b5 b6 b7 bc bs
          a0 a1 a2 a3 a4 a5 a6 a7 ac as s)) :
    replyRecvOperandArmThenTaintKE ctx SeLe4n.arm64DefaultLayout rf extraCaps tid requiredRight
        (fun cap => endpointReplyRecvLongCheckedArmR ctx rf len extraCaps label tid
          executingCore cap) operand st kOk kRefused kStep =
      match replyRecvLongOperandArmThenTaintR ctx rf len extraCaps label tid executingCore
          requiredRight operand st with
      | .ok ((), s) => kOk s
      | .error (e, s) => kErr e s := by
  have hS' : (fun n c w b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as e s =>
      kErr e (replyRecvEntryRefusalStepW n c w tid b0 b1 b2 b3 b4 b5 b6 b7 bc bs
        a0 a1 a2 a3 a4 a5 a6 a7 ac as s)) = kStep := by
    funext n c w b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as e s
    exact (hS n c w b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as e s).symm
  have hR' : kErr = kRefused := funext fun e => funext fun s => (hR e s).symm
  subst hS' hR'
  unfold replyRecvOperandArmThenTaintKE replyRecvLongOperandArmThenTaintR
  cases operand with
  | none => rfl
  | some cap =>
    dsimp only
    cases SeLe4n.Kernel.capTargetsReservedKernelObject cap
    · cases syscallTargetAccepted .replyRecv st cap
      · rfl
      · cases cap.hasRight requiredRight
        · rfl
        · dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, withTaintWordsAt]
          cases endpointReplyRecvLongCheckedArmR ctx rf len extraCaps label tid executingCore
              cap st with
          | error p => obtain ⟨e, s⟩ := p; rfl
          | ok p => obtain ⟨⟨⟩, s⟩ := p; rfl
    · rfl

/-- A routed reply-receive's refusal of its arm reported as words: the reply
capability's failed lookup at the reply register's address, any other refusal
under the entry's resolved continuation (`replyLookupRefusalW`). -/
@[inline] def replyRecvRoutedArmErrW (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → SystemState :=
  replyLookupRefusalW true tid (replyRecvReplyAddr rf) (entryReportPushErrorW 1)
    (entryReportPushLookupAtW (replyRecvReplyAddr rf).word)

/-- A routed reply-receive's refusal of the receive capability with nothing
written: the after-reply route where the reply answers on the state the
refusal carries (`replyRecvAfterReplyRoutedArm`, its message words the long
reply's where `long`), the entry's lookup report otherwise. -/
@[inline] def replyRecvRoutedLookupRefusal (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (capWord : UInt64)
    (rf : SeLe4n.RegisterFile) (long : Bool) (length extraCaps label : Nat) (e : KernelError)
    (s : SystemState) : SystemState :=
  if replyRecvAnswersOn ctx tid (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg)
      extraCaps s then
    replyRecvAfterReplyRoutedArm ctx executingCore tid capWord
      (cond long (longReplyRegs s tid rf length)
        (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf))
      length extraCaps label s
  else entryReportLookup e s

/-- **The routed reply-receive's refusal decoder, on words**: a refusal of
the reply-receive's routed arms, its error as its discriminant `d` and payload
words (as `noCapRefusalW` hands them to its error continuation), reported as
the entry's operand route reports it (`replyRecvRoutedArmErrW`).  Out of line,
and nothing it takes is a cell, so no exit builds a `KernelError`. -/
@[noinline] def replyRecvRoutedRefusalW (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile)
    (d : Nat) (w0 w1 w2 w3 w4 : UInt64) (s : SystemState) : SystemState :=
  replyRecvRoutedArmErrW tid rf d w0 w1 w2 w3 w4 s

/-- The routed reply-receive's refusal of the operand's empty slot
(`noCapRefusalW`'s lookup continuation, its error the closed
`.invalidCapability 0`), out of line. -/
@[noinline] def replyRecvRoutedRefusalL (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (capWord : UInt64)
    (rf : SeLe4n.RegisterFile) (long : Bool) (length extraCaps label : Nat) (e : KernelError)
    (s : SystemState) : SystemState :=
  replyRecvRoutedLookupRefusal ctx executingCore tid capWord rf long length extraCaps label e s

/-- **The routed reply-receive's refusal**: the refusal told apart first, each
error with a payload down to its words (`noCapRefusalW`), so the join point a
routed arm's refusals meet at is specialised per constructor and builds
nothing; then, in each of the two continuations, the entry route's refusal
step on the state (`replyRecvEntryRefusalStepW`, the identity where
`answered` is `0`, as for every refusal before the checked arm) and the
decoder (`replyRecvRoutedRefusalW`, `replyRecvRoutedRefusalL`).  Each
continuation is two calls, so the join point it becomes is shared by every
exit rather than copied into each (`replyRecvRoutedRefusal_eq`). -/
@[inline] def replyRecvRoutedRefusal (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (capWord : UInt64)
    (rf : SeLe4n.RegisterFile) (long : Bool) (length extraCaps label : Nat)
    (answered sourceCode : Nat) (awaited : Bool)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (bc : Nat) (bs : Bool)
    (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool)
    (noCap : Bool) (e : KernelError) (s : SystemState) : SystemState :=
  noCapRefusalW noCap (entryReportPushOk 1)
    (fun d w0 w1 w2 w3 w4 s' => replyRecvRoutedRefusalW tid rf d w0 w1 w2 w3 w4
      (replyRecvEntryRefusalStepW answered sourceCode awaited tid
        b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as s'))
    (fun e' s' => replyRecvRoutedRefusalL ctx executingCore tid capWord rf long length extraCaps
      label e' (replyRecvEntryRefusalStepW answered sourceCode awaited tid
        b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as s'))
    (.error (e, s))

/-- **A refusal's state mapped before it is told apart is mapped in each
continuation**: `noCapRefusalW` reads only the refusal's error, so a map of
its state commutes with the split.  Unconditional. -/
theorem noCapRefusalW_error_map {β : Type} (noCap : Bool) (kOk : SystemState → β)
    (kErr : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → SystemState → β)
    (onLookup : KernelError → SystemState → β) (f : SystemState → SystemState)
    (e : KernelError) (s : SystemState) :
    noCapRefusalW noCap kOk (fun d w0 w1 w2 w3 w4 s' => kErr d w0 w1 w2 w3 w4 (f s'))
        (fun e' s' => onLookup e' (f s')) (.error (e, s)) =
      noCapRefusalW noCap kOk kErr onLookup (.error (e, f s)) := by
  cases e with
  | failedLookup w lf => cases lf <;> rfl
  | _ => rfl

/-- **The decoder is the operand route's report of the refusal, the refusal
step applied to its state.**  Unconditional. -/
theorem replyRecvRoutedRefusal_eq (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (capWord : UInt64)
    (rf : SeLe4n.RegisterFile) (long : Bool) (length extraCaps label : Nat)
    (answered sourceCode : Nat) (awaited : Bool)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (bc : Nat) (bs : Bool)
    (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool)
    (noCap : Bool) (e : KernelError) (s : SystemState) :
    replyRecvRoutedRefusal ctx executingCore tid capWord rf long length extraCaps label
        answered sourceCode awaited b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as
        noCap e s =
      noCapRefusalW noCap (entryReportPushOk 1) (replyRecvRoutedArmErrW tid rf)
        (replyRecvRoutedLookupRefusal ctx executingCore tid capWord rf long length extraCaps
          label)
        (.error (e, replyRecvEntryRefusalStepW answered sourceCode awaited tid
          b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as s)) :=
  noCapRefusalW_error_map noCap (entryReportPushOk 1) (replyRecvRoutedArmErrW tid rf)
    (replyRecvRoutedLookupRefusal ctx executingCore tid capWord rf long length extraCaps label)
    _ e s

/-- The decoder on a refusal before the checked arm, its words `0`, is the
operand route's report of the refusal on the state it carries. -/
theorem replyRecvRoutedRefusal_zero (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (capWord : UInt64)
    (rf : SeLe4n.RegisterFile) (long : Bool) (length extraCaps label : Nat)
    (noCap : Bool) (e : KernelError) (s : SystemState) :
    replyRecvRoutedRefusal ctx executingCore tid capWord rf long length extraCaps label
        0 0 false 0 0 0 0 0 0 0 0 0 false 0 0 0 0 0 0 0 0 0 false noCap e s =
      noCapRefusalW noCap (entryReportPushOk 1) (replyRecvRoutedArmErrW tid rf)
        (replyRecvRoutedLookupRefusal ctx executingCore tid capWord rf long length extraCaps
          label) (.error (e, s)) :=
  replyRecvRoutedRefusal_eq ctx executingCore tid capWord rf long length extraCaps label
    0 0 false 0 0 0 0 0 0 0 0 0 false 0 0 0 0 0 0 0 0 0 false noCap e s

/-- **The routed reply-receive's operand arm**: the continuation-form arm
(`replyRecvOperandArmThenTaintKE`) over the short or long checked arm
`checked`, a
commit reported, every refusal handed to the one decoder
(`replyRecvRoutedRefusal`), a refusal before the checked arm with its words
`0` (`replyRecvRoutedArmK_eq`, `replyRecvLongRoutedArmK_eq`).  Inlined as
written into the routed arm. -/
@[macro_inline] def replyRecvRoutedArmK (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (capWord : UInt64)
    (rf : SeLe4n.RegisterFile) (long : Bool) (length extraCaps label : Nat)
    (checked : Capability → RefusalCarrying Unit)
    (c : Option Capability) (s : SystemState) (noCap : Bool) : SystemState :=
  replyRecvOperandArmThenTaintKE ctx SeLe4n.arm64DefaultLayout rf extraCaps tid
    (syscallRequiredRight .replyRecv) checked c s (entryReportPushOk 1)
    (fun e s' => noCapRefusalW noCap (entryReportPushOk 1)
      (fun d w0 w1 w2 w3 w4 s'' => replyRecvRoutedRefusalW tid rf d w0 w1 w2 w3 w4 s'')
      (fun e' s'' => replyRecvRoutedRefusalL ctx executingCore tid capWord rf long length
        extraCaps label e' s'') (.error (e, s')))
    (fun n c' w b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as e s' =>
      replyRecvRoutedRefusal ctx executingCore tid capWord rf long length extraCaps label n c' w
        b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as noCap e s')

/-- **The routed operand arm is the reply-receive's arm, reported**: the
operand route's report (`noCapRefusalW`) of `replyRecvOperandArmThenTaintR`'s
result.  Unconditional. -/
theorem replyRecvRoutedArmK_eq (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (capWord : UInt64)
    (rf : SeLe4n.RegisterFile) (length extraCaps label : Nat)
    (c : Option Capability) (s : SystemState) (noCap : Bool) :
    replyRecvRoutedArmK ctx executingCore tid capWord rf false length extraCaps label
        (fun cap => endpointReplyRecvCheckedArmR ctx SeLe4n.arm64DefaultLayout rf length
          extraCaps label tid executingCore cap) c s noCap =
      noCapRefusalW noCap (entryReportPushOk 1) (replyRecvRoutedArmErrW tid rf)
        (replyRecvRoutedLookupRefusal ctx executingCore tid capWord rf false length extraCaps
          label)
        (replyRecvOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout rf length extraCaps label
          tid executingCore (syscallRequiredRight .replyRecv) c s) := by
  unfold replyRecvRoutedArmK
  rw [replyRecvOperandArmThenTaintKE_eq ctx SeLe4n.arm64DefaultLayout rf length extraCaps label
    tid executingCore _ c s _
    (fun e s' => noCapRefusalW noCap (entryReportPushOk 1) (replyRecvRoutedArmErrW tid rf)
      (replyRecvRoutedLookupRefusal ctx executingCore tid capWord rf false length extraCaps
        label) (.error (e, s'))) _ _ (by intros; rfl)
    (by intros; exact replyRecvRoutedRefusal_eq ..)]
  rcases replyRecvOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout rf length extraCaps label
    tid executingCore (syscallRequiredRight .replyRecv) c s with ⟨e, s'⟩ | ⟨⟨⟩, s'⟩ <;> rfl

/-- The long routed operand arm is the long reply-receive's arm, reported.
Unconditional. -/
theorem replyRecvLongRoutedArmK_eq (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (capWord : UInt64)
    (rf : SeLe4n.RegisterFile) (length extraCaps label : Nat)
    (c : Option Capability) (s : SystemState) (noCap : Bool) :
    replyRecvRoutedArmK ctx executingCore tid capWord rf true length extraCaps label
        (fun cap => endpointReplyRecvLongCheckedArmR ctx rf length extraCaps label tid
          executingCore cap) c s noCap =
      noCapRefusalW noCap (entryReportPushOk 1) (replyRecvRoutedArmErrW tid rf)
        (replyRecvRoutedLookupRefusal ctx executingCore tid capWord rf true length extraCaps
          label)
        (replyRecvLongOperandArmThenTaintR ctx rf length extraCaps label tid executingCore
          (syscallRequiredRight .replyRecv) c s) := by
  unfold replyRecvRoutedArmK
  rw [replyRecvLongOperandArmThenTaintKE_eq ctx rf length extraCaps label
    tid executingCore _ c s _
    (fun e s' => noCapRefusalW noCap (entryReportPushOk 1) (replyRecvRoutedArmErrW tid rf)
      (replyRecvRoutedLookupRefusal ctx executingCore tid capWord rf true length extraCaps
        label) (.error (e, s'))) _ _ (by intros; rfl)
    (by intros; exact replyRecvRoutedRefusal_eq ..)]
  rcases replyRecvLongOperandArmThenTaintR ctx rf length extraCaps label
    tid executingCore (syscallRequiredRight .replyRecv) c s with ⟨e, s'⟩ | ⟨⟨⟩, s'⟩ <;> rfl

end SeLe4n.Kernel
