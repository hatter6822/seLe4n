-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Receive
import SeLe4n.Kernel.ContextLenders.Fault
import SeLe4n.Kernel.ContextLenders.Reply
import SeLe4n.Kernel.KernelRecords.Dispatch
import SeLe4n.Kernel.QueueLabels.Dispatch

/-! # The checked dispatch's IPC arms carry the lenders' flow

WS-SX SX8.  The twin of `KernelRecords/Dispatch.lean`'s IPC arms for
`lendingLabelsEqual`.  The receive (seL4-MCS `receiveIPC`): the busy reply's
holder cancelled, the bound notification completed or the context returned, the
rendezvous, and the lend of the dequeued `Call`'s context to the receiver: a
creating site, whose label equation (the receiver labelled as the caller it
dequeues) the receive gate and the dequeued caller's wait give (WS-SX SX17): the
gate, two-way, gives the receiver the endpoint's label, and the caller headed
the endpoint's send queue, so it was blocked sending or calling on it
(`queueHeadBlockedConsistent`) and has the endpoint's label too
(`blockedSenderLabelsEqual`, SX11's waiters carried to the receive's state).

The steps that link or lend read the chain facts at the state they run from
(`LendersPremises`), as premises (`docs/REGISTERED_DEBT.md` table C,
"`ipcReachable` is not carried across a trace of kernel entries", owner WS-PK).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **The receive leg's dequeued thread**: the receiver itself (the leg blocked
and dequeued nobody), or the head of the endpoint's send queue at the state the
leg runs from, with its record there (a head with no record fails the pop). -/
theorem endpointReceiveDualWithCapsOnCore_dequeued_cases {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {r : Option SeLe4n.ReplyId} {ec : CoreId} {s st1 : SystemState}
    {dequeued : SeLe4n.ThreadId} {summ : CapTransferSummary} {sgi : Option (CoreId × Concurrency.SgiKind)}
    (h : endpointReceiveDualWithCapsOnCore epId tid r ec s = (st1, .ok (dequeued, summ, sgi))) :
    dequeued = tid ∨ ∃ ep tcb, s.objects[epId]? = some (.endpoint ep) ∧
      ep.sendQ.head = some dequeued ∧ lookupTcb s dequeued = some tcb := by
  cases hEp : s.getEndpoint? epId with
  | none =>
    exact .inl (endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_receiver_of_blocked epId tid r ec
      s st1 dequeued summ sgi (by simp [receiveRendezvousSender?, hEp]) h)
  | some ep =>
    cases hH : ep.sendQ.head with
    | none =>
      exact .inl (endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_receiver_of_blocked epId tid r
        ec s st1 dequeued summ sgi (by simp [receiveRendezvousSender?, hEp, hH]) h)
    | some sender =>
      have hD := endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_head epId tid r ec s st1
        dequeued summ sgi ep sender hEp hH h
      subst hD
      have hEpObj := (SystemState.getEndpoint?_eq_some_iff s epId ep).mp hEp
      cases hT : lookupTcb s dequeued with
      | some tcb => exact .inr ⟨ep, tcb, hEpObj, hH, rfl⟩
      | none =>
        exfalso
        have hPop : endpointQueuePopHead epId false s = .error .objectNotFound := by
          unfold endpointQueuePopHead SystemState.getObject?
          simp [hEpObj, hH, hT]
        unfold endpointReceiveDualWithCapsOnCore endpointReceiveDualOnCore at h
        simp [hEp, hH, hPop] at h

/-- **The receive take's label equation** (a creating site, WS-SX SX17): the
receiver the gate admitted has the endpoint's label, and the thread its leg
dequeues is itself or a sender blocked on that endpoint, which has the
endpoint's label too. -/
theorem endpointReceiveDualWithCapsOnCore_dequeued_labelEq {ctx : LabelingContext}
    {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {r : Option SeLe4n.ReplyId} {ec : CoreId}
    {s st1 : SystemState} {dequeued : SeLe4n.ThreadId} {summ : CapTransferSummary}
    {sgi : Option (CoreId × Concurrency.SgiKind)}
    (hQ : queueHeadBlockedConsistent s) (hW : blockedSenderLabelsEqual ctx s)
    (hG : ctx.threadLabelOf tid = ctx.endpointLabelOf epId)
    (h : endpointReceiveDualWithCapsOnCore epId tid r ec s = (st1, .ok (dequeued, summ, sgi))) :
    ctx.threadLabelOf tid = ctx.threadLabelOf dequeued := by
  rcases endpointReceiveDualWithCapsOnCore_dequeued_cases h with rfl | ⟨ep, tcb, hEp, hH, hT⟩
  · rfl
  · rw [hG, hW dequeued tcb epId hT
      ((hQ epId ep dequeued tcb hEp (lookupTcb_some_objects s dequeued tcb hT)).2 hH)]

/-- **What the receive's lending steps read at the states they run from**: the
donation chain's shape where the rendezvous runs (after seL4-MCS's return), and
the chain facts where the lend runs (after the rendezvous), for the reply
object the arm resolved.  Premises read off those states (WS-PK row above). -/
def ReceiveLendersPremises (stC : SystemState) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) (epId : SeLe4n.ObjId) (ec : CoreId) : Prop :=
  donationChainWellFormed
      (receiveReturnSchedContext (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid) ∧
    ∀ r, resolveRecvReplyId gate decoded stC = .ok r → ∀ st1 res,
      endpointReceiveDualWithCapsOnCore epId tid r ec
        (receiveReturnSchedContext (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid)
        = (st1, res) → LendersPremises st1

/-- **A receive run on its busy-reply-cancelled state carries the lenders'
flow** (seL4-MCS `receiveIPC`): the holder's cancel, then the notification's
completion, the non-blocking miss, or the return, the rendezvous and the lend at
the receive's admission, whose label equation the receive gate (`hG`) and the
waiters at the dispatcher's state (`hW`, carried to the rendezvous) give. -/
theorem receiveResolvedArm_lendersStage (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (gate : SyscallGate) (epId : SeLe4n.ObjId)
    (st st' : SystemState) (hInv : st.objects.invExt) (hIpc : ipcInvariantFull st)
    (hCaller : CallerReady st tid) (hW : endpointWaitersLabelsEqual ctx st)
    (hG : ctx.threadLabelOf tid = ctx.endpointLabelOf epId)
    (hP : ReceiveLendersPremises (cancelRecvBusyReply ctx tid gate decoded ec st) tid gate
      decoded epId ec)
    (h : receiveResolvedArm ctx decoded gate tid epId ec
      (cancelRecvBusyReply ctx tid gate decoded ec st) = .ok ((), st')) :
    LendersStage ctx st st' := by
  unfold receiveResolvedArm at h
  have hSC : LendersStep ctx st (cancelRecvBusyReply ctx tid gate decoded ec st) ∧
      queueHeadBlockedConsistent (cancelRecvBusyReply ctx tid gate decoded ec st) ∧
      CallerReady (cancelRecvBusyReply ctx tid gate decoded ec st) tid := by
    rcases cancelRecvBusyReply_cases ctx tid gate decoded ec st with e | ⟨hd, hne, e⟩ <;> rw [e]
    · exact ⟨.refl hInv, hIpc.queueHeadBlockedConsistent, hCaller⟩
    · exact ⟨LendersStep.cancelReplyHolder st hd ec hInv,
        cancelReplyHolder_queueHeadBlockedConsistent st hd ec hInv (.of_ipcInvariantFull hIpc),
        hCaller.cancelReplyHolder hInv (Ne.symm hne)⟩
  obtain ⟨hS, hQC, hCC⟩ := hSC
  have hIC := hS.invExt
  have hWC := (QueueLabelsFrame.cancelRecvBusyReply ctx tid gate decoded ec st hInv).waiters hW
  generalize cancelRecvBusyReply ctx tid gate decoded ec st = stC at h hP hS hIC hQC hCC hWC
  by_cases hSig : receiveCompletesSignal ctx stC tid = true
  · cases hRes : resolveRecvReplyId gate decoded stC with
    | error _ => rw [hRes] at h; cases h
    | ok r =>
    rw [hRes] at h
    simp only [hSig, ↓reduceIte] at h
    exact hS.stage.trans (LendersStep.completeSignalArm hIC hCC.notParked h).stage
  simp only [Bool.not_eq_true] at hSig
  by_cases hNb : receiveFindsNothing (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC
      epId = true
  · cases hRes : resolveRecvReplyId gate decoded stC with
    | error _ => rw [hRes] at h; cases h
    | ok r =>
    rw [hRes] at h
    simp only [hSig, Bool.false_eq_true, hNb, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq,
      true_and] at h
    subst h
    exact hS.stage.trans (LendersFrame.writeReturnFrameToTcb _ _ _ hIC).stage
  simp only [Bool.not_eq_true] at hNb
  simp only [hSig, hNb, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  rename_i r hRes
  split at h
  · rename_i st1 dequeued summ sgi hRecv
    split at h
    · cases h
    rename_i stDon hHand
    cases h
    obtain ⟨hChainR, hMid⟩ := hP
    have hIR := receiveReturnSchedContext_objects_invExt
      (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid hIC
    have hReady : ∀ x, stC.getTcb? tid = some x → x.ipcState = .ready := fun x hx => by
      obtain ⟨t, hT, hR⟩ := hCC
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hx] at hT
      cases hT
      exact hR
    have hPM := hMid r hRes st1 _ hRecv
    have hWR := (QueueLabelsFrame.receiveReturnSchedContext
      (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid hIC).waiters hWC
    have hQR := (receiveReturnSchedContext_receivePremises
      (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid hIC hQC hCC).2.1
    have hEq := endpointReceiveDualWithCapsOnCore_dequeued_labelEq hQR hWR.1 hG hRecv
    refine hS.stage.trans ((LendersStep.receiveReturnSchedContext
      (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid hIC).stage.trans ?_)
    intro hF
    have h1 := endpointReceiveDualWithCapsOnCore_preserves_lendingLabelsEqual epId tid r ec _ hIR
      hChainR hF
    rw [hRecv] at h1
    have h2 := applyReceiveRendezvousHandoff_preserves_lendingLabelsEqual hPM h1
      (fun _ _ _ => hEq) hHand
    exact LendersStage.of_kept (chainObjectsKept.stageDeliveredMessage _ _ _
      (applyReceiveRendezvousHandoff_preserves_objects_invExt _ _ _ _ _ hPM.invExt hHand)) h2
  · cases h

/-- **A reply-receive whose receive completes its bound notification**: the
reply leg, then the completion on the replier the reply leg left `.ready`. -/
theorem LendersStep.replyRecvCompletesSignalArm {ctx : LabelingContext}
    {tid prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState} (hInv : st.objects.invExt)
    (hLink : replyCallerLinkageReciprocal st)
    (h : SeLe4n.Kernel.replyRecvCompletesSignalArm ctx tid prevCaller label msg grant c st
      = .ok ((), st')) : LendersStep ctx st st' := by
  obtain ⟨st1, hR, hOr⟩ := replyRecvCompletesSignalArm_split h
  have F := LendersStep.replyTransferOnCoreChecked hInv hLink hR
  rcases hOr with rfl | ⟨_, ⟨t, hT, hReady⟩, hC⟩
  · exact F
  · exact F.andThen fun hI => LendersStep.completeSignalArm hI
      (CallerReady.notParked ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mp hT, hReady⟩) hC

end SeLe4n.Kernel
