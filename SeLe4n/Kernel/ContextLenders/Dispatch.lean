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

/-! # The checked dispatch's IPC arms carry the lenders' flow

WS-SX SX8.  The twin of `KernelRecords/Dispatch.lean`'s IPC arms for
`contextLendersFlow`.  The receive (seL4-MCS `receiveIPC`): the busy reply's
holder cancelled, the bound notification completed or the context returned, the
rendezvous, and the lend of the dequeued `Call`'s context at the receive's lend
admission (`receiveLendAdmits`).  That admission is read on the state the arm is
handed, and the lend happens two steps later, so the bridge
(`receiveLendAdmits_flows_dequeued`) carries it: the thread the rendezvous lends
from is the send queue's head the admission read, blocked on a call there, and
holding there the context it holds when it lends.

The steps that link or lend read the chain facts at the state they run from
(`LendersPremises`), as premises (`docs/REGISTERED_DEBT.md` table C,
"`ipcReachable` is not carried across a trace of kernel entries", owner WS-PK).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **The receive's lend admission covers the lend it gates**: where the
admission, read on the state the arm is handed, passes, the context a dequeued
`Call` lends at the rendezvous is one its caller's label flows to.  The block
path dequeues the receiver itself, which lends nothing to itself; a dequeued
plain send is no `Call` after the rendezvous; a dequeued call is the send
queue's head the admission read, holding the same context, since seL4-MCS's
return before the receive clears only the receiver's binding. -/
theorem receiveLendAdmits_flows_dequeued {ctx : LabelingContext} {stC st1 : SystemState}
    {epId : SeLe4n.ObjId} {tid dequeued : SeLe4n.ThreadId} {blocks : Bool}
    {r : Option SeLe4n.ReplyId} {ec : CoreId} {summ : CapTransferSummary}
    {sgi : Option (CoreId × Concurrency.SgiKind)}
    (hIC : stC.objects.invExt) (hQC : queueHeadBlockedConsistent stC)
    (hReady : ∀ x, stC.getTcb? tid = some x → x.ipcState = .ready)
    (hRecv : endpointReceiveDualWithCapsOnCore epId tid r ec
      (receiveReturnSchedContext blocks stC tid) = (st1, .ok (dequeued, summ, sgi)))
    (hAdm : receiveLendAdmits ctx stC epId = true) :
    rendezvousDequeuedCall st1 dequeued = true →
      ∀ s, callDonationSchedContext? st1 dequeued tid = some s →
      securityFlowsTo (ctx.threadLabelOf dequeued) (ctx.objectLabelOf s.toObjId) = true := by
  intro hCallPost s hS
  have hIR := receiveReturnSchedContext_objects_invExt blocks stC tid hIC
  obtain ⟨hQR, -, hEB⟩ := receiveReturnSchedContext_receiveLegFacts blocks stC tid hIC hQC hReady
  cases hSender : receiveRendezvousSender? (receiveReturnSchedContext blocks stC tid) epId with
  | none =>
    have hDq := endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_receiver_of_blocked epId tid r ec
      _ st1 dequeued summ sgi hSender hRecv
    subst hDq
    rw [callDonationSchedContext?_self] at hS
    cases hS
  | some sender =>
    obtain ⟨ep, hEp, hHead⟩ : ∃ ep, (receiveReturnSchedContext blocks stC tid).getEndpoint? epId
        = some ep ∧ ep.sendQ.head = some sender := by
      unfold receiveRendezvousSender? at hSender
      cases hE : (receiveReturnSchedContext blocks stC tid).getEndpoint? epId with
      | none => rw [hE] at hSender; simp at hSender
      | some ep => rw [hE] at hSender; exact ⟨ep, rfl, hSender⟩
    have hDq := endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_head epId tid r ec _ st1 dequeued
      summ sgi ep sender hEp hHead hRecv
    subst hDq
    have hBind := endpointReceiveDualWithCapsOnCore_sameSchedContextBindings_of_rendezvous epId tid
      r ec _ ep dequeued hIR hEp hHead
    rw [hRecv] at hBind
    have hPre := callDonationSchedContext?_some_of_sameSchedContextBindings hBind dequeued tid s hS
    obtain ⟨-, ⟨cT, hCT, hCB⟩⟩ := callDonationSchedContext?_some_char _ _ _ _ hPre
    have hEpObj := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    have hCTo := lookupTcb_some_objects _ _ _ hCT
    rcases (hQR epId ep dequeued cT hEpObj hCTo).2 hHead with hSend | hCall
    · have hNo := endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_blockedOnSend epId tid r ec
        _ ep dequeued cT epId hIR hEp hHead hCT hSend
      rw [hRecv] at hNo
      simp only [hCallPost] at hNo
      cases hNo
    · obtain ⟨y, hy, hxy⟩ := receiveReturnSchedContext_tcb blocks stC tid hIC _ cT hCTo
      have hYL := lookupTcb_of_objects_of_not_reserved _ _ _ hy (lookupTcb_some_not_reserved _ _ _ hCT)
      have hYCall : y.ipcState = .blockedOnCall epId := by
        rcases hxy with rfl | rfl <;> exact hCall
      have hYB : y.schedContextBinding.scId? = some s := by
        rcases hxy with rfl | rfl
        · exact hCB
        · simp [TCB.schedContextBinding, SchedContextBinding.scId?] at hCB
      rw [receiveLendAdmits_of_head ((SystemState.getEndpoint?_eq_some_iff _ _ _).mpr
        (hEB epId ep hEpObj)) hHead hYL hYCall] at hAdm
      exact callLendAdmits_flows_of_binding hAdm hYL hYB

/-- **What the receive's lending steps read at the states they run from**: the
donation chain's shape where the rendezvous runs (after seL4-MCS's return), and
the chain facts where the lend runs (after the rendezvous), for the reply
object the arm resolved.  Premises read off those states (WS-PK row above). -/
def ReceiveLendersPremises (stC : SystemState) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (decoded : SyscallDecodeResult) (epId : SeLe4n.ObjId) (ec : CoreId) : Prop :=
  donationChainWellFormed
      (receiveReturnSchedContext (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid) ∧
    ∀ r, resolveRecvReplyId gate decoded stC = .ok r → ∀ st1 res,
      endpointReceiveDualWithCapsOnCore epId tid r ec
        (receiveReturnSchedContext (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid)
        = (st1, res) → LendersPremises st1

/-- **A receive run on its busy-reply-cancelled state carries the lenders'
flow** (seL4-MCS `receiveIPC`): the holder's cancel, then the notification's
completion, the non-blocking miss, or the return, the rendezvous and the lend at
the receive's admission. -/
theorem receiveResolvedArm_lendersStage (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (gate : SyscallGate) (epId : SeLe4n.ObjId)
    (st st' : SystemState) (hInv : st.objects.invExt) (hIpc : ipcInvariantFull st)
    (hCaller : CallerReady st tid)
    (hP : ReceiveLendersPremises (cancelRecvBusyReply ctx tid gate decoded ec st) tid gate decoded
      epId ec)
    (h : receiveResolvedArm ctx decoded gate tid epId ec
      (cancelRecvBusyReply ctx tid gate decoded ec st) = .ok ((), st')) :
    LendersStage ctx st st' := by
  unfold receiveResolvedArm at h
  have hSC : LendersFrame st (cancelRecvBusyReply ctx tid gate decoded ec st) ∧
      queueHeadBlockedConsistent (cancelRecvBusyReply ctx tid gate decoded ec st) ∧
      CallerReady (cancelRecvBusyReply ctx tid gate decoded ec st) tid := by
    rcases cancelRecvBusyReply_cases ctx tid gate decoded ec st with e | ⟨hd, hne, e⟩ <;> rw [e]
    · exact ⟨.refl hInv, hIpc.queueHeadBlockedConsistent, hCaller⟩
    · exact ⟨LendersFrame.cancelReplyHolder st hd ec hInv,
        cancelReplyHolder_queueHeadBlockedConsistent st hd ec hInv (.of_ipcInvariantFull hIpc),
        hCaller.cancelReplyHolder hInv (Ne.symm hne)⟩
  obtain ⟨hS, hQC, hCC⟩ := hSC
  have hIC := hS.invExt
  generalize cancelRecvBusyReply ctx tid gate decoded ec st = stC at h hP hS hIC hQC hCC
  by_cases hSig : receiveCompletesSignal ctx stC tid = true
  · cases hRes : resolveRecvReplyId gate decoded stC with
    | error _ => rw [hRes] at h; cases h
    | ok r =>
    rw [hRes] at h
    simp only [hSig, ↓reduceIte] at h
    exact hS.stage.trans (LendersFrame.completeSignalArm hIC hCC.notParked h).stage
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
    refine hS.stage.trans ((LendersFrame.receiveReturnSchedContext
      (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid hIC).stage.trans ?_)
    intro hF
    have h1 := endpointReceiveDualWithCapsOnCore_preserves_contextLendersFlow epId tid r ec _ hIR
      hChainR hF
    rw [hRecv] at h1
    have h2 := applyReceiveRendezvousHandoff_preserves_contextLendersFlow hPM h1
      (fun hL => receiveLendAdmits_flows_dequeued hIC hQC hReady hRecv hL) hHand
    exact LendersStage.of_kept (chainObjectsKept.stageDeliveredMessage _ _ _
      (applyReceiveRendezvousHandoff_preserves_objects_invExt _ _ _ _ _ hPM.invExt hHand)) h2
  · cases h

/-- **A reply-receive whose receive completes its bound notification**: the
reply leg, then the completion on the replier the reply leg left `.ready`. -/
theorem LendersFrame.replyRecvCompletesSignalArm {ctx : LabelingContext}
    {tid prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.replyRecvCompletesSignalArm ctx tid prevCaller label msg grant c st
      = .ok ((), st')) : LendersFrame st st' := by
  obtain ⟨st1, hR, hOr⟩ := replyRecvCompletesSignalArm_split h
  have F := LendersFrame.replyTransferOnCoreChecked hInv hR
  rcases hOr with rfl | ⟨_, ⟨t, hT, hReady⟩, hC⟩
  · exact F
  · exact F.andThen fun hI => LendersFrame.completeSignalArm hI
      (CallerReady.notParked ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mp hT, hReady⟩) hC

end SeLe4n.Kernel
