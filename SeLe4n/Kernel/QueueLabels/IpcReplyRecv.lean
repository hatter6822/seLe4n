-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.QueueLabels.IpcReply
import SeLe4n.Kernel.KernelRecords.Dispatch

/-! # The reply-receive: a creator

WS-SX SX11.2.  The reply-receive answers its caller (a frame: the caller is
made `.ready`, or its fault outcome applied), then receives on its endpoint,
which blocks at most the server on that endpoint.  The `.replyRecv` arm checks
`endpointFlowGate` on the server and the endpoint, two-way, before it runs, so
the new waiter has the endpoint's label.  The proof follows the records' own
(`KernelRecords/Dispatch.lean`, `RecordsStep.endpointReplyRecvAnsweringOnCore`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **The queue labels hold at the reply step's state** (WS-SX SX32, the state a
refused receive reports, WS-SX SX33): the reply leg, the pop, the transfer and
the caller's answer write no endpoint queue and no waiter's IPC state. -/
theorem QueueLabelsFrame.replyRecvReplyStep {answer : Option Architecture.FaultReplyOutcome}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId}
    {msg : IpcMessage} {grant : Bool} {c : CoreId} {st st1 : SystemState}
    {sgi : Option (CoreId × Concurrency.SgiKind)}
    {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {st1q : SystemState}
    (hInv : st.objects.invExt)
    (hR : _root_.SeLe4n.Kernel.endpointReplyOnCore tid prevCaller msg c st = (st1, .ok sgi))
    (hPop : _root_.SeLe4n.Kernel.replyRecvPopDonation rid prevCaller st1 = .ok (r, st1q)) :
    QueueLabelsFrame st (replyRecvReplyStepState answer st tid grant rid prevCaller st1) := by
  have A := QueueLabelsFrame.endpointReplyOnCore (replier := tid) (target := prevCaller)
    (msg := msg) (c := c) hInv
  rw [hR] at A
  obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer st tid prevCaller grant st1q
  rw [replyRecvReplyStepState_eq_of_ok hPop hX]
  have F0 := RecordsFrame.replyRecvPopDonation A.invExt hPop
  have F1 := F0.trans (RecordsFrame.receiveTransferCaps F0.invExt
    (by rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX; exact hX))
  have FA : QueueLabelsFrame st1p (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) := by
    cases answer with
    | none => exact .of_frame (RecordsFrame.stageDeliveredMessage _ prevCaller xs.capInfo F1.invExt)
    | some o => exact QueueLabelsFrame.faultReplyApplyOnCore _ prevCaller o F1.invExt
  exact (A.trans (.of_frame F1)).trans FA

namespace QueueLabelsGrowFrame

/-- **The reply-receive blocks at most its server, on its endpoint.** -/
theorem endpointReplyRecvAnsweringOnCore
    {answer : Option Architecture.FaultReplyOutcome} {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState} {summary : CapTransferSummary}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg
      grant c st = .ok (summary, st')) :
    QueueLabelsGrowFrame tid epId st st' := by
  unfold _root_.SeLe4n.Kernel.endpointReplyRecvAnsweringOnCore at h
  dsimp only at h
  have A := QueueLabelsFrame.endpointReplyOnCore (replier := tid) (target := prevCaller)
    (msg := msg) (c := c) hInv
  revert h A
  cases hR : _root_.SeLe4n.Kernel.endpointReplyOnCore tid prevCaller msg c st with
  | mk st1 res1 =>
  cases res1 with
  | error _ => intro h; cases h
  | ok sgi =>
  intro h A
  dsimp only at h A
  split at h
  · cases h
  rename_i ret st1q hPop
  obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer st tid prevCaller grant st1q
  rw [hX] at h
  dsimp only at h
  have F0 := RecordsFrame.replyRecvPopDonation A.invExt hPop
  have F1 := F0.trans (RecordsFrame.receiveTransferCaps F0.invExt
    (by rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX; exact hX))
  -- The caller is answered in the reply step, before the receive leg.
  generalize hA : replyRecvAnswerCaller answer st1p prevCaller xs.capInfo = st1a at h
  have FA : QueueLabelsFrame st1p st1a := by
    subst hA
    cases answer with
    | none => exact .of_frame (RecordsFrame.stageDeliveredMessage _ prevCaller xs.capInfo F1.invExt)
    | some o => exact QueueLabelsFrame.faultReplyApplyOnCore _ prevCaller o F1.invExt
  have FR : RecordsFrame st1a (receiveReturnSchedContext true st1a tid) :=
    receiveReturnSchedContext_induct (fun a b => RecordsFrame a b) true st1a tid
      (RecordsFrame.refl FA.invExt)
      (fun vS _ _ _ => RecordsFrame.schedContextReturnPerform vS tid FA.invExt)
  have S2 := endpointReceiveDualWithCapsOnCore (endpointId := epId) (receiver := tid)
    (replyId := some rid) (c := c) FR.invExt
  revert h S2
  generalize _root_.SeLe4n.Kernel.endpointReceiveDualWithCapsOnCore epId tid (some rid)
    c (receiveReturnSchedContext true st1a tid) = r2
  obtain ⟨st2, res2⟩ := r2
  cases res2 with
  | error _ => intro h; cases h
  | ok q =>
  obtain ⟨nextThread, summ, _⟩ := q
  intro h S2
  dsimp only at h S2
  split at h
  · cases h
  rename_i st3 hPost
  cases h
  have F3 := RecordsFrame.replyRecvPostReceiveDonation S2.invExt hPost
  have F4 := RecordsFrame.applyReceiveLegPipHandoff st3 tid nextThread
    ((recordedReplyServer? st prevCaller).getD tid) c F3.invExt
  exact ((((A.trans (.of_frame F1)).trans FA).trans (.of_frame FR)).thenGrow S2).thenFrame
    (.of_frame (F3.trans F4))

end QueueLabelsGrowFrame

namespace QueueLabelsStage

variable {ctx : LabelingContext}

/-- **A reply-receive admitted by its gate carries the waiters' labels**: the
receive leg's gate, two-way, gives the server the endpoint's label. -/
theorem replyRecvTransferOnCore {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage}
    {grant : Bool} {c : CoreId} {st st' : SystemState} {summary : CapTransferSummary}
    (hInv : st.objects.invExt)
    (hGate : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true)
    (h : _root_.SeLe4n.Kernel.replyRecvTransferOnCore epId tid rid prevCaller label msg
      grant c st = .ok (summary, st')) : QueueLabelsStage ctx st st' := by
  unfold _root_.SeLe4n.Kernel.replyRecvTransferOnCore at h
  exact (QueueLabelsGrowFrame.endpointReplyRecvAnsweringOnCore hInv h).stage
    (endpointFlowGate_implies_eq ctx epId _ _ hGate).symm

end QueueLabelsStage

end SeLe4n.Kernel
