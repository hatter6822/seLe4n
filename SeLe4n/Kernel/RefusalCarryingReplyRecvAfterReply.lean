-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ReplyRecvReceiveAfterReply
import SeLe4n.Kernel.RefusalCarryingReplyRecvTransfer

/-!
# ReplyRecv in seL4's order, each refusal carrying the state it stopped in

The answering reply-receive of `ReplyRecvReceiveAfterReply` (the reply step,
then the receive capability's lookup, verdicts and flow gate on the state the
reply left, then the receive), with each refusal carrying the state its step
stopped in, as `replyRecvTransferOnCoreR` carries it for the entry order.

seL4's `handleInvocation` has completed the reply before `handleRecv` looks the
receive capability up, so a refusal of that lookup leaves the reply's effects
as they are.  Both arms give it one outcome, the nothing-received outcome of
D53 (the holder's deschedule where the pop handed a context back, and the
recorded server's priority-inheritance reversion):

* in the composite, the pop defers the deschedule, so a refusal of the
  receive's endpoint reports `replyRecvNothingReceived` on the state the
  caller's answer left, as a refused receive leg does;
* where the receive completes a bound notification, the reply is the `.reply`
  arm's transition (`replyTransferOnCoreChecked`), whose pop deschedules the
  holder (`applyReplyDonationOnCore`) and whose tail reverts the recorded
  server's priority inheritance (`endpointReplyCrossCoreDispatch`): the state
  it returns is already that outcome, and a later refusal carries it as it is.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode

/-- **The state a refusal-carrying computation stopped in**: the state its
refusal carries, and the state handed in where it does not refuse. -/
def RefusalCarrying.stoppedState {α : Type} (r : RefusalCarrying α) (st : SystemState) :
    SystemState :=
  match r st with
  | .error (_, s) => s
  | .ok _ => st

/-- A refusal-carrying computation that is `k` with the refusal's state
forgotten is `k` reporting the state it stopped in. -/
theorem RefusalCarrying.eq_reporting_of_mapError {α : Type} {r : RefusalCarrying α}
    {k : Kernel α} {st : SystemState} (h : (r st).mapError Prod.fst = k st) :
    r st = RefusalCarrying.ofKernelReporting (RefusalCarrying.stoppedState r) k st := by
  unfold RefusalCarrying.ofKernelReporting RefusalCarrying.stoppedState
  rw [← h]
  cases r st with
  | error es => obtain ⟨e, s⟩ := es; rfl
  | ok a => rfl

/-- **The state an answering reply-receive's refusal reports, in seL4's
order**: keyed on the reply it answers (`replyRecvAnsweringReply?`), the state
the refusing step stopped in, the receive's endpoint read after the reply
(`replyRecvReceiveEndpoint`); the state handed in where the reply answers no
caller, since the receive then runs alone. -/
def replyRecvAfterReplyAnsweringReport (ctx : LabelingContext) (gate : SyscallGate)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) : SystemState :=
  match replyRecvAnsweringReply? ctx gate decoded tid st with
  | none => st
  | some (rid, prevCaller, replyBadge, replyGrant) =>
      RefusalCarrying.stoppedState
        (replyRecvAnsweringThenR ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid
          executingCore rid prevCaller replyBadge replyGrant) st

/-- An answering reply-receive in seL4's order reports, on a refusal, the
state its refusing step stopped in (`replyRecvAfterReplyAnsweringReport`). -/
theorem replyRecvAnsweringThenR_eq_reporting {ctx : LabelingContext} {gate : SyscallGate}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {replyBadge : Option SeLe4n.Badge}
    {replyGrant : Bool} {st : SystemState}
    (hAns : replyRecvAnsweringReply? ctx gate decoded tid st =
      some (rid, prevCaller, replyBadge, replyGrant)) :
    replyRecvAnsweringThenR ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid executingCore
        rid prevCaller replyBadge replyGrant st =
      RefusalCarrying.ofKernelReporting
        (fun _ => replyRecvAfterReplyAnsweringReport ctx gate decoded tid executingCore st)
        (replyRecvAnsweringThen ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid
          executingCore rid prevCaller replyBadge replyGrant) st := by
  have h := RefusalCarrying.eq_reporting_of_mapError
    (replyRecvAnsweringThenR_eq ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid
      executingCore rid prevCaller replyBadge replyGrant st)
  rw [h]
  unfold replyRecvAfterReplyAnsweringReport
  rw [hAns]
  rfl

/-! ### The routed reply-receive, its receive capability refused on entry

The routed entry checks a reply-receive's receive capability on entry, as every
operand route does.  Where the reply answers a caller and that check refuses,
seL4 has already replied (`handleInvocation` before `handleRecv`), so the route
runs the reply step and reads the receive capability on the state it left
(`replyRecvRoutedR`); every other case runs the operand route `k` handed in. -/

/-- **A reply-receive whose reply answers and whose receive capability the
entry refuses**: the caller's gate and the reply it answers, or `none`. -/
def replyRecvRefusedOnEntry? (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (st : SystemState) :
    Option (SyscallGate × SeLe4n.ReplyId × SeLe4n.ThreadId × Option SeLe4n.Badge × Bool) :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    match replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st with
    | some (rid, prevCaller, replyBadge, replyGrant) =>
      match replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st with
      | .ok _ => none
      | .error _ => some (replyRecvCallerGate decoded tid tcb, rid, prevCaller, replyBadge, replyGrant)
    | none => none
  | _ => none

/-- **A routed reply-receive in seL4's order**: where the reply answers and the
entry refuses the receive capability (`replyRecvRefusedOnEntry?`), the caller's
currency check, the reply step and the receive capability read after it
(`replyRecvAnsweringThenR`); `k` otherwise.  A completed route takes the taint
step of a receive capability read after the reply (`replyRecvAfterReplyTaint`);
a refused one reports each leg's edge where that leg delivered
(`replyRecvAfterReplyRefusalTaint`).  A specification: the compiled route runs it out of
line. -/
noncomputable def replyRecvRoutedR (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (k : RefusalCarrying Unit) :
    RefusalCarrying Unit := fun st =>
  match replyRecvRefusedOnEntry? ctx decoded tid st with
  | none => k st
  | some (gate, rid, prevCaller, replyBadge, replyGrant) =>
    if !(st.scheduler.currentOnCore executingCore).isEqSome tid then .error (.illegalState, st)
    else
    match replyRecvAnsweringThenR ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid
        executingCore rid prevCaller replyBadge replyGrant st with
    | .error (e, s) =>
      .error (e, replyRecvAfterReplyRefusalTaint ctx decoded tid executingCore gate rid prevCaller
        replyBadge replyGrant st s)
    | .ok ((), stPost) =>
      .ok ((), replyRecvAfterReplyTaint ctx decoded tid executingCore gate rid prevCaller replyBadge
        replyGrant st stPost)

/-- **The state a routed reply-receive's refusal reports**: the after-reply
route's (`replyRecvAfterReplyAnsweringReport`) where it runs, `kReport`'s
otherwise. -/
def replyRecvRoutedReport (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (kReport : SystemState → SystemState) (st : SystemState) : SystemState :=
  match replyRecvRefusedOnEntry? ctx decoded tid st with
  | none => kReport st
  | some (gate, rid, prevCaller, replyBadge, replyGrant) =>
    if st.scheduler.currentOnCore executingCore ≠ some tid then st
    else replyRecvAfterReplyRefusalTaint ctx decoded tid executingCore gate rid prevCaller
      replyBadge replyGrant st
      (replyRecvAfterReplyAnsweringReport ctx gate decoded tid executingCore st)

/-- No after-reply route: the entry's order holds for every caller TCB. -/
theorem replyRecvRefusedOnEntry?_none {ctx : LabelingContext} {decoded : SyscallDecodeResult}
    {tid : SeLe4n.ThreadId} {st : SystemState}
    (h : replyRecvRefusedOnEntry? ctx decoded tid st = none) (tcb : TCB)
    (hT : st.getObject? tid.toObjId = some (.tcb tcb)) :
    replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st = none ∨
      ∃ epId, replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st =
        .ok epId := by
  unfold replyRecvRefusedOnEntry? at h
  rw [hT] at h
  dsimp only at h
  cases hA : replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st with
  | none => exact .inl rfl
  | some q =>
    rw [hA] at h
    obtain ⟨rid, prevCaller, replyBadge, replyGrant⟩ := q
    dsimp only at h
    cases hE : replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st with
    | ok ep => exact .inr ⟨ep, rfl⟩
    | error e => rw [hE] at h; cases h

/-- An after-reply route: the caller is a TCB, its reply answers, and the entry
refuses its receive capability. -/
theorem replyRecvRefusedOnEntry?_some {ctx : LabelingContext} {decoded : SyscallDecodeResult}
    {tid : SeLe4n.ThreadId} {st : SystemState} {gate : SyscallGate} {rid : SeLe4n.ReplyId}
    {prevCaller : SeLe4n.ThreadId} {replyBadge : Option SeLe4n.Badge} {replyGrant : Bool}
    (h : replyRecvRefusedOnEntry? ctx decoded tid st =
      some (gate, rid, prevCaller, replyBadge, replyGrant)) :
    ∃ tcb e, st.getObject? tid.toObjId = some (.tcb tcb) ∧
      gate = replyRecvCallerGate decoded tid tcb ∧
      replyRecvAnsweringReply? ctx gate decoded tid st =
        some (rid, prevCaller, replyBadge, replyGrant) ∧
      replyRecvReceiveEndpoint ctx gate tid st = .error e := by
  unfold replyRecvRefusedOnEntry? at h
  cases hT : st.getObject? tid.toObjId with
  | none => rw [hT] at h; cases h
  | some o =>
    rw [hT] at h
    cases o with
    | tcb tcb =>
      dsimp only at h
      cases hA : replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st with
      | none => rw [hA] at h; cases h
      | some q =>
        rw [hA] at h
        obtain ⟨rid', prevCaller', replyBadge', replyGrant'⟩ := q
        dsimp only at h
        cases hE : replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st with
        | ok ep => rw [hE] at h; cases h
        | error e =>
          rw [hE] at h
          cases h
          exact ⟨tcb, e, rfl, rfl, hA, hE⟩
    | _ => cases h

/-- **The routed reply-receive is the checked dispatch, reporting the state its
refusing step stopped in**, given that `k` is, wherever the entry's order holds
(`hk`): the after-reply route is `dispatchSyscallChecked`'s answering arm whose
entry refuses the receive capability (`dispatchReplyRecvAfterReply`), and its
refusal reports `replyRecvAfterReplyAnsweringReport`. -/
theorem replyRecvRoutedR_eq {ctx : LabelingContext} {decoded : SyscallDecodeResult}
    {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId} {k : RefusalCarrying Unit}
    {kReport : SystemState → SystemState} {st : SystemState}
    (hRR : decoded.syscallId = .replyRecv)
    (hk : (∀ tcb, st.getObject? tid.toObjId = some (.tcb tcb) →
        replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st = none ∨
        ∃ epId, replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st =
          .ok epId) →
      k st = RefusalCarrying.ofKernelReporting kReport
        (dispatchSyscallChecked ctx decoded tid executingCore) st) :
    replyRecvRoutedR ctx decoded tid executingCore k st =
      RefusalCarrying.ofKernelReporting
        (replyRecvRoutedReport ctx decoded tid executingCore kReport)
        (dispatchSyscallChecked ctx decoded tid executingCore) st := by
  unfold replyRecvRoutedR
  cases hR : replyRecvRefusedOnEntry? ctx decoded tid st with
  | none =>
    dsimp only
    rw [hk (replyRecvRefusedOnEntry?_none hR)]
    unfold RefusalCarrying.ofKernelReporting replyRecvRoutedReport
    rw [hR]
  | some q =>
    obtain ⟨gate, rid, prevCaller, replyBadge, replyGrant⟩ := q
    obtain ⟨tcb, e, hT, hG, hA, hE⟩ := replyRecvRefusedOnEntry?_some hR
    dsimp only
    unfold RefusalCarrying.ofKernelReporting replyRecvRoutedReport dispatchSyscallChecked
    rw [hR]
    dsimp only
    by_cases hCur : st.scheduler.currentOnCore executingCore = some tid
    · have hIs : (st.scheduler.currentOnCore executingCore).isEqSome tid = true :=
        (threadId_isEqSome_iff _ _).2 hCur
      have hNot : ¬ (st.scheduler.currentOnCore executingCore ≠ some tid) := fun h => h hCur
      have hNY : decoded.syscallId ≠ .yield := by rw [hRR]; decide
      rw [if_neg (by simp only [hIs, Bool.not_true, Bool.false_eq_true, not_false_eq_true]),
        if_neg hNot, if_neg hNot, if_neg hNY, hT]
      dsimp only
      rw [dispatchSyscallArmChecked_replyRecv hRR]
      subst hG
      unfold replyRecvCallerGate at hA hE ⊢
      unfold dispatchReplyRecvAfterReply
      rw [hA]
      dsimp only
      rw [hE]
      dsimp only
      rw [replyRecvAnsweringThenR_eq_reporting hA]
      have hT : ∀ stPost, checkedArmTaint ctx decoded tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
            requiredRight := syscallRequiredRight decoded.syscallId } st stPost =
          replyRecvAfterReplyTaint ctx decoded tid executingCore
            { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
              requiredRight := syscallRequiredRight decoded.syscallId }
            rid prevCaller replyBadge replyGrant st stPost := by
        intro stPost
        unfold checkedArmTaint
        rw [if_pos hRR, hA]
        dsimp only
        rw [hE]
      simp only [hT]
      unfold RefusalCarrying.ofKernelReporting
      generalize replyRecvAnsweringThen ctx _ decoded tid executingCore rid prevCaller replyBadge
        replyGrant st = X
      cases X with
      | error e => rfl
      | ok p => obtain ⟨⟨⟩, stPost⟩ := p; rfl
    · have hIs : (st.scheduler.currentOnCore executingCore).isEqSome tid = false := by
        cases h : (st.scheduler.currentOnCore executingCore).isEqSome tid
        · rfl
        · exact absurd ((threadId_isEqSome_iff _ _).1 h) hCur
      rw [if_pos (by simp only [hIs, Bool.not_false]), if_pos hCur, if_pos hCur]

/-- A decode in the fields a reply-receive's after-reply route reads: the
operand and reply addresses, the message registers, and the message info's
length, extra-capability count and label. -/
def replyRecvDecodeNorm (d : SyscallDecodeResult) : SyscallDecodeResult :=
  { capAddr := d.capAddr,
    msgInfo := { length := d.msgInfo.length, extraCaps := d.msgInfo.extraCaps,
                 label := d.msgInfo.label },
    syscallId := d.syscallId, msgRegs := d.msgRegs, replyCPtr := d.replyCPtr }

/-- **The decode a routed reply-receive stands for**, built from its routed
operands. -/
def replyRecvRoutedDecode (capAddr : SeLe4n.CPtr) (msgRegs : Array SeLe4n.RegValue)
    (replyCPtr : SeLe4n.CPtr) (len extraCaps label : Nat) : SyscallDecodeResult :=
  { capAddr := capAddr, msgInfo := { length := len, extraCaps := extraCaps, label := label },
    syscallId := .replyRecv, msgRegs := msgRegs, replyCPtr := replyCPtr }

theorem replyRecvRoutedDecode_eq_norm {decoded : SyscallDecodeResult}
    (hRR : decoded.syscallId = .replyRecv) :
    replyRecvRoutedDecode decoded.capAddr decoded.msgRegs decoded.replyCPtr
        decoded.msgInfo.length decoded.msgInfo.extraCaps decoded.msgInfo.label =
      replyRecvDecodeNorm decoded := by
  unfold replyRecvRoutedDecode replyRecvDecodeNorm
  rw [hRR]

/-- The after-reply route reads the decode only in its normal fields. -/
theorem replyRecvRoutedR_norm (ctx : LabelingContext) (d : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (k : RefusalCarrying Unit) :
    replyRecvRoutedR ctx (replyRecvDecodeNorm d) tid executingCore k =
      replyRecvRoutedR ctx d tid executingCore k := rfl

/-- The after-reply route's report reads the decode only in its normal fields. -/
theorem replyRecvRoutedReport_norm (ctx : LabelingContext) (d : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (kReport : SystemState → SystemState) :
    replyRecvRoutedReport ctx (replyRecvDecodeNorm d) tid executingCore kReport =
      replyRecvRoutedReport ctx d tid executingCore kReport := rfl

/-- **Whether a reply-receive's receive capability was looked up after its
reply** (WS-SX SX36.1): the decode is a reply-receive whose reply answers and
whose receive capability the entry refuses (`replyRecvRefusedOnEntry?`), so the
lookup the capability fault reads ran on the state the reply step left, not on
the entry's. -/
def replyRecvLooksUpAfterReply (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (st : SystemState) : Bool :=
  if decoded.syscallId = .replyRecv then (replyRecvRefusedOnEntry? ctx decoded tid st).isSome
  else false

theorem replyRecvLooksUpAfterReply_of_ne {ctx : LabelingContext} {decoded : SyscallDecodeResult}
    {tid : SeLe4n.ThreadId} {st : SystemState} (h : decoded.syscallId ≠ .replyRecv) :
    replyRecvLooksUpAfterReply ctx decoded tid st = false := by
  unfold replyRecvLooksUpAfterReply
  rw [if_neg h]

theorem replyRecvLooksUpAfterReply_of_none {ctx : LabelingContext} {decoded : SyscallDecodeResult}
    {tid : SeLe4n.ThreadId} {st : SystemState}
    (h : replyRecvRefusedOnEntry? ctx decoded tid st = none) :
    replyRecvLooksUpAfterReply ctx decoded tid st = false := by
  unfold replyRecvLooksUpAfterReply
  rw [h]
  by_cases hR : decoded.syscallId = .replyRecv
  · rw [if_pos hR]; rfl
  · rw [if_neg hR]

theorem replyRecvLooksUpAfterReply_of_some {ctx : LabelingContext} {decoded : SyscallDecodeResult}
    {tid : SeLe4n.ThreadId} {st : SystemState} {q}
    (hRR : decoded.syscallId = .replyRecv)
    (h : replyRecvRefusedOnEntry? ctx decoded tid st = some q) :
    replyRecvLooksUpAfterReply ctx decoded tid st = true := by
  unfold replyRecvLooksUpAfterReply
  rw [if_pos hRR, h]
  rfl

/-- The after-reply lookup's test reads the decode only in its normal fields. -/
theorem replyRecvRefusedOnEntry?_norm (ctx : LabelingContext) (d : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (st : SystemState) :
    replyRecvRefusedOnEntry? ctx (replyRecvDecodeNorm d) tid st =
      replyRecvRefusedOnEntry? ctx d tid st := rfl

end SeLe4n.Kernel
