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
`lendingLabelsEqual`.  The receive (seL4-MCS `receiveIPC`): the busy reply's
holder cancelled, the bound notification completed or the context returned, the
rendezvous, and the lend of the dequeued `Call`'s context to the receiver: a
creating site, whose label equation (the receiver labelled as the caller it
dequeues) the arm's premise pack carries at the state the lend runs from
(`ReceiveLendersPremises`; WS-SX SX17 discharges it from the receive gate and
the dequeued caller's wait).

The steps that link or lend read the chain facts at the state they run from
(`LendersPremises`), as premises (`docs/REGISTERED_DEBT.md` table C,
"`ipcReachable` is not carried across a trace of kernel entries", owner WS-PK).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **What the receive's lending steps read at the states they run from**: the
donation chain's shape where the rendezvous runs (after seL4-MCS's return), and
the chain facts where the lend runs (after the rendezvous), for the reply
object the arm resolved, with the lend's label equation (a creating site: the
receiver labelled as the `Call` it dequeues, WS-SX SX17 discharges it).
Premises read off those states (WS-PK row above). -/
def ReceiveLendersPremises (ctx : LabelingContext) (stC : SystemState) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) (epId : SeLe4n.ObjId) (ec : CoreId) : Prop :=
  donationChainWellFormed
      (receiveReturnSchedContext (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid) ∧
    ∀ r, resolveRecvReplyId gate decoded stC = .ok r → ∀ st1 res,
      endpointReceiveDualWithCapsOnCore epId tid r ec
        (receiveReturnSchedContext (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid)
        = (st1, res) → LendersPremises st1 ∧
      ∀ dequeued summ sgi, res = .ok (dequeued, summ, sgi) →
        rendezvousDequeuedCall st1 dequeued = true →
        ∀ s, callDonationSchedContext? st1 dequeued tid = some s →
          ctx.threadLabelOf tid = ctx.threadLabelOf dequeued

/-- **A receive run on its busy-reply-cancelled state carries the lenders'
flow** (seL4-MCS `receiveIPC`): the holder's cancel, then the notification's
completion, the non-blocking miss, or the return, the rendezvous and the lend at
the receive's admission. -/
theorem receiveResolvedArm_lendersStage (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (gate : SyscallGate) (epId : SeLe4n.ObjId)
    (st st' : SystemState) (hInv : st.objects.invExt) (hIpc : ipcInvariantFull st)
    (hCaller : CallerReady st tid)
    (hP : ReceiveLendersPremises ctx (cancelRecvBusyReply ctx tid gate decoded ec st) tid gate
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
  generalize cancelRecvBusyReply ctx tid gate decoded ec st = stC at h hP hS hIC hQC hCC
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
    obtain ⟨hPM, hEq⟩ := hMid r hRes st1 _ hRecv
    refine hS.stage.trans ((LendersStep.receiveReturnSchedContext
      (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid hIC).stage.trans ?_)
    intro hF
    have h1 := endpointReceiveDualWithCapsOnCore_preserves_lendingLabelsEqual epId tid r ec _ hIR
      hChainR hF
    rw [hRecv] at h1
    have h2 := applyReceiveRendezvousHandoff_preserves_lendingLabelsEqual hPM h1
      (fun _ hCall s hs => hEq dequeued summ sgi rfl hCall s hs) hHand
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
