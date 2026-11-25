-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Dispatch

/-! # The reply-receive's answering leg carries equal lending labels

WS-SX SX8.  seL4-MCS `handleReplyRecv`: `doReplyTransfer` (the reply leg, the
pop of the answered frame's context, the reply's capability transfer), then
`receiveIPC` (the return of a notification's context, the rendezvous and the
lend of the dequeued `Call`'s context).  WS-SX SX16: the pop is a labelled step
(`LendersStep`), its owner the reply's recorded caller, which the frame's
lending labels give at the pre-reply state and the reply leg's links shrink
carries (`calledFrame_labelEq`); the lend is a creating site whose label
equation the receive leg's gate and the dequeued caller's wait give (WS-SX
SX17, `endpointReceiveDualWithCapsOnCore_dequeued_labelEq`), the waiters and
the queue heads carried from the reply-receive's state to the receive leg's.  The chain facts the dispatch reads are premises
(`docs/REGISTERED_DEBT.md` table C, "`ipcReachable` is not carried across a trace
of kernel entries", owner WS-PK).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace LendersFrame

/-- The deschedule of the thread the pop unbound. -/
theorem replyRecvHolderDeschedule (tid holder : SeLe4n.ThreadId) (st : SystemState)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.replyRecvHolderDeschedule tid holder st) := by
  unfold _root_.SeLe4n.Kernel.replyRecvHolderDeschedule
  split
  · exact refl hInv
  · exact descheduleAtPlacement st holder hInv

/-- The receive leg's priority hand-off. -/
theorem applyReceiveLegPipHandoff (st : SystemState)
    (receiver dequeued alreadyWalked : SeLe4n.ThreadId) (executingCore : CoreId)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.applyReceiveLegPipHandoff st receiver dequeued
      alreadyWalked executingCore) := by
  unfold _root_.SeLe4n.Kernel.applyReceiveLegPipHandoff
  split
  · exact refl hInv
  split
  · exact propagatePipChainCrossCore st receiver executingCore _ hInv
  · exact refl hInv

/-- The answer to the replied-to caller: its delivered message staged, or its
fault answered. -/
theorem replyRecvAnswerCaller (answer : Option Architecture.FaultReplyOutcome)
    (st : SystemState) (prevCaller : SeLe4n.ThreadId) (capInfo : Nat)
    (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.replyRecvAnswerCaller answer st prevCaller capInfo) := by
  cases answer with
  | none =>
    exact of_kept (chainObjectsKept.stageDeliveredMessage _ _ _ hInv)
      (RecordsFrame.stageDeliveredMessage _ _ _ hInv)
  | some o => exact faultReplyApplyOnCore st prevCaller o hInv

end LendersFrame

namespace LendersStep

variable {ctx : LabelingContext}

/-- **The donation pop between the legs** (seL4-MCS `reply_pop` under
`doReplyTransfer`), a labelled step: the return of the head frame's context to
the answered caller, the held pop, or the unheld head's pop, given the answered
caller is labelled as the context the frame heads (the reply-receive proves it
from the frame's recorded caller at the pre-reply state, `calledFrame_labelEq`). -/
theorem replyRecvPopDonation {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {st st' : SystemState} {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.replyRecvPopDonation rid target st = .ok (r, st'))
    (hOwner : ∀ s, replyFrameHeadContext? st rid = some s →
      ctx.threadLabelOf target = ctx.objectLabelOf s.toObjId) :
    LendersStep ctx st st' := by
  unfold _root_.SeLe4n.Kernel.replyRecvPopDonation at h
  split at h
  · rename_i scId holder hHH
    split at h
    · split at h
      · split at h
        · cases h
        · rename_i st1 hRet
          cases h
          exact (returnDonatedSchedContextResolved hInv hRet
            (hOwner scId (replyFrameHeadHolder?_eq_some hHH).1)).andThen fun hI =>
              of_frame (LendersFrame.settleReturnedContext _ _ _ hI)
      · split at h
        · cases h
        · rename_i st1 hK
          cases h
          exact keepDonatedSchedContextResolved hInv hK
    · cases h
  · split at h
    · cases h
    · rename_i st1 hPop
      cases h
      exact popUnheldReplyHead hInv hPop hOwner

end LendersStep

/-- The holder's deschedule writes run-queue links alone. -/
theorem replyRecvHolderDeschedule_objectsAgreeOffRunLinks (tid holder : SeLe4n.ThreadId)
    (st : SystemState) :
    (replyRecvHolderDeschedule tid holder st).objectsAgreeOffRunLinks st := by
  unfold replyRecvHolderDeschedule
  split
  · exact .refl _
  · exact descheduleAtPlacement_objectsAgreeOffRunLinks st holder

/-- **The post-receive half carries equal lending labels**: the lend of the dequeued
`Call`'s context to the receiver (after the holder's deschedule, which writes
run-queue links alone, so the lend and its admission read the same thread
records), or the deschedule, then the priority walk. -/
theorem replyRecvPostReceiveDonation_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {tid recordedServer nextThread : SeLe4n.ThreadId} {serverCore : CoreId}
    {returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {st st' : SystemState}
    (hP : LendersPremises st)
    (hPH : ∀ sc holder, returned? = some (sc, holder) →
      LendersPremises (replyRecvHolderDeschedule tid holder st))
    (hIn : lendingLabelsEqual ctx st)
    (hFlow : rendezvousDequeuedCall st nextThread = true →
      ∀ s, callDonationSchedContext? st nextThread tid = some s →
      ctx.threadLabelOf tid = ctx.threadLabelOf nextThread)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
      = .ok ((), st')) :
    lendingLabelsEqual ctx st' := by
  unfold replyRecvPostReceiveDonation at h
  split at h
  · split at h
    · rename_i hCall
      split at h
      · cases h
      rename_i st2 hD
      cases h
      have hD' : applyReceiveRendezvousDonation st tid nextThread = .ok st2 := by
        unfold applyReceiveRendezvousDonation; rw [hCall]; exact hD
      have h1 := applyReceiveRendezvousDonation_preserves_lendingLabelsEqual hP hIn hFlow hD'
      exact LendersStage.of_kept (chainObjectsKept.propagatePipChainCrossCore _ _ _ _
        (applyReceiveRendezvousDonation_preserves_objects_invExt _ _ _ _ hP.invExt hD')) h1
    · cases h
      exact LendersStage.of_kept (chainObjectsKept.propagatePipChainCrossCore _ _ _ _ hP.invExt)
        hIn
  · rename_i sc holder
    have hRL := replyRecvHolderDeschedule_objectsAgreeOffRunLinks tid holder st
    have hPX := hPH sc holder rfl
    have hInX : lendingLabelsEqual ctx (replyRecvHolderDeschedule tid holder st) :=
      (LendersFrame.replyRecvHolderDeschedule tid holder st hP.invExt).stage hIn
    split at h
    · rename_i hCall
      split at h
      · cases h
      rename_i st2 hD
      cases h
      have hCallX : rendezvousDequeuedCall (replyRecvHolderDeschedule tid holder st) nextThread
          = true := by rw [rendezvousDequeuedCall_of_objectsAgreeOffRunLinks hRL]; exact hCall
      have hD' : applyReceiveRendezvousDonation (replyRecvHolderDeschedule tid holder st) tid
          nextThread = .ok st2 := by
        unfold applyReceiveRendezvousDonation; rw [hCallX]; exact hD
      have h1 := applyReceiveRendezvousDonation_preserves_lendingLabelsEqual hPX hInX
        (fun _ s hS => hFlow hCall s
          (callDonationSchedContext?_some_of_sameSchedContextBindings
            (sameSchedContextBindings.of_objectsAgreeOffRunLinks hRL) nextThread tid s hS)) hD'
      exact LendersStage.of_kept (chainObjectsKept.propagatePipChainCrossCore _ _ _ _
        (applyReceiveRendezvousDonation_preserves_objects_invExt _ _ _ _ hPX.invExt hD')) h1
    · cases h
      have F := LendersFrame.descheduleAtPlacement st holder hP.invExt
      exact (F.andThen fun hI => LendersFrame.propagatePipChainCrossCore _ recordedServer
        serverCore _ hI).stage hIn

/-- **What the reply-receive's answering leg reads at the states it runs
from**: the donation chain's shape where the receive leg runs (after seL4-MCS's
return), the chain facts where the lend runs (after the receive leg, and after
the holder's deschedule where the pop unbound one).  Premises read off those
states (`docs/REGISTERED_DEBT.md` table C, owner WS-PK). -/
def ReplyRecvLendersPremises (st : SystemState)
    (answer : Option Architecture.FaultReplyOutcome) (epId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (grant : Bool) (c : CoreId) : Prop :=
  ∀ st1 sgi, endpointReplyOnCore tid prevCaller msg c st = (st1, .ok sgi) →
    ∀ ret st1q, replyRecvPopDonation rid prevCaller st1 = .ok (ret, st1q) →
    ∀ xs st1p, replyRecvReplyTransfer answer st tid prevCaller grant st1q = .ok (xs, st1p) →
      donationChainWellFormed (receiveReturnSchedContext true st1p tid) ∧
      ∀ st2 res, endpointReceiveDualWithCapsOnCore epId tid (some rid) c
          (receiveReturnSchedContext true st1p tid) = (st2, res) →
        LendersPremises st2 ∧
        ∀ sc holder, ret = some (sc, holder) →
          LendersPremises (replyRecvHolderDeschedule tid holder st2)

/-- **The reply-receive's answering leg carries equal lending labels** (seL4-MCS
`handleReplyRecv`): the reply leg, the pop (a labelled step whose owner is the
reply's recorded caller, read at the pre-reply state through
`calledFrame_labelEq` and carried across the reply leg's links shrink), the
reply's capability transfer, the return, the receive leg, the lend (its label
equation from the receive gate `hG` and the waiters `hW`), the priority
hand-off and the answer to the replied-to caller. -/
theorem endpointReplyRecvAnsweringOnCore_lendersStage {ctx : LabelingContext}
    {answer : Option Architecture.FaultReplyOutcome} {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState} {summary : CapTransferSummary}
    (hInv : st.objects.invExt) (hC : replyAnsweredCaller? st rid = some prevCaller)
    (hQ : queueHeadBlockedConsistent st) (hReady : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready)
    (hW : endpointWaitersLabelsEqual ctx st) (hG : ctx.threadLabelOf tid = ctx.endpointLabelOf epId)
    (hP : ReplyRecvLendersPremises st answer epId tid rid prevCaller msg grant c)
    (h : endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg grant c st
      = .ok (summary, st')) :
    LendersStage ctx st st' := by
  intro hF
  unfold endpointReplyRecvAnsweringOnCore at h
  dsimp only at h
  have A := LendersFrame.endpointReplyOnCore (replier := tid) (target := prevCaller) (msg := msg)
    (c := c) hInv
  have AW := QueueLabelsFrame.endpointReplyOnCore (replier := tid) (target := prevCaller)
    (msg := msg) (c := c) hInv
  revert h A AW
  cases hR : endpointReplyOnCore tid prevCaller msg c st with
  | mk st1 res1 =>
  cases res1 with
  | error _ => intro h; cases h
  | ok sgi =>
  intro h A AW
  dsimp only at h A AW
  have hP1 := hP st1 sgi hR
  split at h
  · cases h
  rename_i ret st1q hPop
  obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer st tid prevCaller grant st1q
  rw [hX] at h
  dsimp only at h
  obtain ⟨hChainR, hP2⟩ := hP1 ret st1q hPop xs st1p hX
  have F0 := LendersStep.replyRecvPopDonation (ctx := ctx) A.invExt hPop
    (calledFrame_labelEq hF.1 hC A.links)
  have hX' := hX
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX'
  have F1 : LendersFrame st1q st1p :=
    LendersFrame.of_kept (chainObjectsKept.receiveTransferCaps F0.invExt hX')
      (RecordsFrame.receiveTransferCaps F0.invExt hX')
  have FR := LendersStep.receiveReturnSchedContext (ctx := ctx) true st1p tid F1.invExt
  have S1 : lendingLabelsEqual ctx (receiveReturnSchedContext true st1p tid) :=
    FR.stage (F1.stage (F0.stage (A.stage hF)))
  have FW0 := RecordsFrame.replyRecvPopDonation AW.invExt hPop
  have FW1 := FW0.trans (RecordsFrame.receiveTransferCaps FW0.invExt hX')
  have hWR := (QueueLabelsFrame.receiveReturnSchedContext true st1p tid FW1.invExt).waiters
    ((QueueLabelsFrame.of_frame FW1).waiters (AW.waiters hW))
  obtain ⟨hQp, hRp, -⟩ := replyRecvReceiveLegFacts hInv hQ hR hPop hX hReady
  have hQR := (receiveReturnSchedContext_receiveLegFacts true st1p tid FW1.invExt hQp hRp).1
  revert h
  cases hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) c
      (receiveReturnSchedContext true st1p tid) with
  | mk st2 res2 =>
  cases res2 with
  | error _ => intro h; cases h
  | ok q =>
  obtain ⟨nextThread, summ, sgi'⟩ := q
  intro h
  dsimp only at h
  split at h
  · cases h
  rename_i st3 hPost
  cases h
  obtain ⟨hP3, hPH⟩ := hP2 st2 _ hRecv
  have hEq := endpointReceiveDualWithCapsOnCore_dequeued_labelEq hQR hWR.1 hG hRecv
  have h1 := endpointReceiveDualWithCapsOnCore_preserves_lendingLabelsEqual epId tid (some rid) c
    _ FR.invExt hChainR S1
  rw [hRecv] at h1
  have h2 := replyRecvPostReceiveDonation_preserves_lendingLabelsEqual hP3 hPH h1
    (fun _ _ _ => hEq) hPost
  have hI3 := (RecordsFrame.replyRecvPostReceiveDonation hP3.invExt hPost).invExt
  have F4 := LendersFrame.applyReceiveLegPipHandoff st3 tid nextThread
    ((recordedReplyServer? st prevCaller).getD tid) c hI3
  exact (F4.andThen fun hI => LendersFrame.replyRecvAnswerCaller answer _ prevCaller _ hI).stage h2

/-- **The `.replyRecv` arm's transition carries equal lending labels**: the
answering leg at the answer the replied-to caller's fault record selects. -/
theorem replyRecvTransferOnCore_lendersStage {ctx : LabelingContext}
    {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool} {c : CoreId}
    {st st' : SystemState} {summary : CapTransferSummary}
    (hInv : st.objects.invExt) (hC : replyAnsweredCaller? st rid = some prevCaller)
    (hQ : queueHeadBlockedConsistent st) (hReady : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready)
    (hW : endpointWaitersLabelsEqual ctx st) (hG : ctx.threadLabelOf tid = ctx.endpointLabelOf epId)
    (hP : ReplyRecvLendersPremises st (replyRecvCallerFaultAnswer? st prevCaller label msg)
      epId tid rid prevCaller
      (replyRecvLegMessage (replyRecvCallerFaultAnswer? st prevCaller label msg) msg) grant c)
    (h : replyRecvTransferOnCore epId tid rid prevCaller label msg grant c st
      = .ok (summary, st')) :
    LendersStage ctx st st' := by
  unfold replyRecvTransferOnCore at h
  exact endpointReplyRecvAnsweringOnCore_lendersStage hInv hC hQ hReady hW hG hP h

end SeLe4n.Kernel
