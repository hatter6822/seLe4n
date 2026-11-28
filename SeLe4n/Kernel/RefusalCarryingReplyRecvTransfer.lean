/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecv
import SeLe4n.Kernel.IPC.CrossCore.CapTransferDelivered

/-!
# The reply-receive's transition, each refusal carrying the state it stopped in

seL4's `SysReplyRecv` replies, then receives, and a receive the kernel refuses
keeps the completed reply (`api/syscall.c`, `case SysReplyRecv`).  The arm's
transition `replyRecvTransferOnCore` is a `Kernel` computation, whose refusal
carries no state, so a caller reporting what a refused reply-receive left
behind would have to keep the state it handed over alive across the reply leg,
and the leg's first store would then copy the object table.

`replyRecvTransferOnCoreR` is that transition with each refusal carrying the
state its step stopped in (WS-SX SX34, D60, D61):

* the pop's admission (`replyRecvPopAdmits`) and the reply leg refuse before
  any write, and carry the state handed in;
* the pop (off `objects.invExt` only, D60) carries the state its stores reached
  (`replyRecvPopDonationR`);
* the reply's capability transfer never refuses (`receiveTransferCaps_ok`);
* a refused receive, and a refused post-receive donation, report the
  nothing-received outcome (`replyRecvNothingReceived`: the recorded server's
  priority-inheritance reversion, after the holder's deschedule where the pop
  handed a context back, D53) on the state the refusing step returned, D60's
  option (b).

It is the transition with the refusal's state forgotten, with no assumption
(`replyRecvTransferOnCoreR_eq`); the state a refusal carries is
`replyRecvTransferStoppedState`, the report of a refused reply-receive.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The reply-receive composite after its entry-state reads, each refusal
carrying the state its step stopped in**: `endpointReplyRecvAnsweringBody`
with the pop and the post-receive donation in their refusal-carrying forms,
the reply's transfer as its result, and a refused receive or post-receive
donation reporting the nothing-received outcome on the state that step
returned.  Out of line, as the body is, so its arguments are computed before
the leg runs and the entry state is handed to the leg alone. -/
@[noinline] def endpointReplyRecvAnsweringBodyR (answer : Option Architecture.FaultReplyOutcome)
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : Concurrency.CoreId) (recordedServer : SeLe4n.ThreadId)
    (req : Option (Capability × Array SeLe4n.CPtr)) (target : Option (TCB × Option CSpaceAddr)) :
    RefusalCarrying CapTransferSummary := fun st =>
  match endpointReplyOnCore tid prevCaller msg executingCore st with
  | (s, .error e) => .error (e, s)
  | (st1, .ok _replySgi) =>
    match replyRecvPopDonationR rid prevCaller st1 with
    | .error es => .error es
    | .ok (returnedSc?, st1q) =>
      match receiveTransferCapsDone req none target st1q with
      | (replySummary, st1p) =>
      match endpointReceiveDualWithCapsOnCore epId tid (some rid) executingCore
          (receiveReturnSchedContext true
            (replyRecvAnswerCaller answer st1p prevCaller replySummary.capInfo) tid) with
      | (s, .error e) =>
          .error (e, replyRecvNothingReceived recordedServer executingCore returnedSc? s)
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonationR tid recordedServer nextThread executingCore
              returnedSc? st2 with
          | .error (e, s) =>
              .error (e, replyRecvNothingReceived recordedServer executingCore returnedSc? s)
          | .ok ((), st3) =>
              .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread recordedServer
                executingCore)

theorem endpointReplyRecvAnsweringBodyR_eq (answer : Option Architecture.FaultReplyOutcome)
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : Concurrency.CoreId) (recordedServer : SeLe4n.ThreadId)
    (req : Option (Capability × Array SeLe4n.CPtr)) (target : Option (TCB × Option CSpaceAddr))
    (st : SystemState) :
    (endpointReplyRecvAnsweringBodyR answer epId tid rid prevCaller msg executingCore
        recordedServer req target st).mapError Prod.fst =
      endpointReplyRecvAnsweringBody answer epId tid rid prevCaller msg executingCore
        recordedServer req target st := by
  unfold endpointReplyRecvAnsweringBodyR endpointReplyRecvAnsweringBody
  simp only [← replyRecvPopDonationR_eq, receiveTransferCaps_eq_done,
    ← replyRecvPostReceiveDonationR_eq]
  repeat' (first | rfl | (split <;> (try (rename_i h; simp only [h, refusalCarrying_mapError_error,
      refusalCarrying_mapError_ok]))))

/-- **The `.replyRecv` arm's transition, each refusal carrying the state its
step stopped in**: `replyRecvTransferOnCore` with the composite in its
refusal-carrying form, its entry-state reads taken first
(`endpointReplyRecvAnsweringOnCoreChecked`'s).  A refused pop admission
carries the state handed in, since it precedes every write. -/
def replyRecvTransferOnCoreR (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (label : Nat) (msg : IpcMessage)
    (grant : Bool) (executingCore : Concurrency.CoreId) : RefusalCarrying CapTransferSummary :=
  fun st =>
    if replyRecvPopAdmits st rid prevCaller then
      let answer := replyRecvCallerFaultAnswer? st prevCaller label msg
      endpointReplyRecvAnsweringBodyR answer epId tid rid prevCaller
        (replyRecvLegMessage answer msg) executingCore
        ((recordedReplyServer? st prevCaller).getD tid)
        (if answer.isSome then none else replyCapRequest st tid grant)
        (receiverCapTarget? st prevCaller) st
    else .error (.invalidArgument 0, st)

/-- The refusal-carrying transition is the transition with the refusal's state
forgotten, with no assumption. -/
theorem replyRecvTransferOnCoreR_eq (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (label : Nat) (msg : IpcMessage)
    (grant : Bool) (executingCore : Concurrency.CoreId) (st : SystemState) :
    (replyRecvTransferOnCoreR epId tid rid prevCaller label msg grant executingCore st).mapError
        Prod.fst =
      replyRecvTransferOnCore epId tid rid prevCaller label msg grant executingCore st := by
  unfold replyRecvTransferOnCoreR replyRecvTransferOnCore
  split
  · rw [endpointReplyRecvAnsweringOnCore_eq_checked]
    exact endpointReplyRecvAnsweringBodyR_eq _ _ _ _ _ _ _ _ _ _ st
  · rfl

/-- **The state a refused reply-receive transition reports**: the state its
refusing step stopped in (`replyRecvTransferOnCoreR`), and the state handed in
where it does not refuse. -/
def replyRecvTransferStoppedState (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (label : Nat) (msg : IpcMessage)
    (grant : Bool) (executingCore : Concurrency.CoreId) (st : SystemState) : SystemState :=
  match replyRecvTransferOnCoreR epId tid rid prevCaller label msg grant executingCore st with
  | .error (_, s) => s
  | .ok _ => st

/-- The refusal-carrying transition reports, on a refusal, the transition's
refusal with its stopped state (`replyRecvTransferStoppedState`). -/
theorem replyRecvTransferOnCoreR_eq_reporting (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (label : Nat) (msg : IpcMessage)
    (grant : Bool) (executingCore : Concurrency.CoreId) (st : SystemState) :
    replyRecvTransferOnCoreR epId tid rid prevCaller label msg grant executingCore st =
      RefusalCarrying.ofKernelReporting
        (replyRecvTransferStoppedState epId tid rid prevCaller label msg grant executingCore)
        (replyRecvTransferOnCore epId tid rid prevCaller label msg grant executingCore) st := by
  have h := replyRecvTransferOnCoreR_eq epId tid rid prevCaller label msg grant executingCore st
  unfold RefusalCarrying.ofKernelReporting replyRecvTransferStoppedState
  rw [← h]
  cases replyRecvTransferOnCoreR epId tid rid prevCaller label msg grant executingCore st with
  | error es => obtain ⟨e, s⟩ := es; rfl
  | ok r => rfl

/-- The refusal-carrying transition as the transition, its refusal carrying the
stopped state (`replyRecvTransferOnCoreR_eq_reporting`, the report unfolded). -/
theorem replyRecvTransferOnCoreR_eq_match (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (label : Nat) (msg : IpcMessage)
    (grant : Bool) (executingCore : Concurrency.CoreId) (st : SystemState) :
    replyRecvTransferOnCoreR epId tid rid prevCaller label msg grant executingCore st =
      match replyRecvTransferOnCore epId tid rid prevCaller label msg grant executingCore st with
      | .error e =>
          .error (e, replyRecvTransferStoppedState epId tid rid prevCaller label msg grant
            executingCore st)
      | .ok r => .ok r := by
  rw [replyRecvTransferOnCoreR_eq_reporting]
  unfold RefusalCarrying.ofKernelReporting
  cases replyRecvTransferOnCore epId tid rid prevCaller label msg grant executingCore st <;> rfl

end SeLe4n.Kernel
