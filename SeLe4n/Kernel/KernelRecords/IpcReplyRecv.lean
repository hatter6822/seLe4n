-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.IpcStages
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecv
import SeLe4n.Kernel.IPC.CrossCore.ReplyWaitersDispatch
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Ipc

/-!
# The reply-receive keeps the records

WS-ZA ZA6.37.  `.replyRecv` is the reply leg, the donation pop, the receive leg,
the reply leg's capability transfer, the post-receive donation, the receive
leg's priority hand-off and the two stagers.  Every step between the legs writes
scheduling contexts, run queues, the scheduler, or (the transfer) a receive
slot's CNode and the derivation tree only, so each is a records frame.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsFrame

/-- The donation pop between the legs: a return of the head frame's context or
the unheld head's pop. -/
theorem replyRecvPopDonation {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {st st' : SystemState} {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.replyRecvPopDonation rid target st = .ok (r, st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.replyRecvPopDonation at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · cases h
      · rename_i st1 hRet
        cases h
        have F := returnDonatedSchedContextResolved hInv hRet
        exact F.trans (settleReturnedContext _ _ _ F.invExt)
    · cases h
  · split at h
    · cases h
    · rename_i st1 hPop
      cases h
      exact popUnheldReplyHead hInv hPop

/-- The deschedule of the thread the pop unbound. -/
theorem replyRecvHolderDeschedule (tid holder : SeLe4n.ThreadId) (st : SystemState)
    (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.replyRecvHolderDeschedule tid holder st) := by
  unfold _root_.SeLe4n.Kernel.replyRecvHolderDeschedule
  split
  · exact refl hInv
  · exact descheduleAtPlacement st holder hInv

/-- The post-receive donation and the chain walk. -/
theorem replyRecvPostReceiveDonation {tid recordedServer nextThread : SeLe4n.ThreadId}
    {serverCore : CoreId} {returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.replyRecvPostReceiveDonation tid recordedServer nextThread
      serverCore returned? st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.replyRecvPostReceiveDonation at h
  split at h
  · cases h
    exact propagatePipChainCrossCore st recordedServer serverCore _ hInv
  · rename_i holder
    split at h
    · split at h
      · cases h
      · rename_i st2 hD
        cases h
        have H := replyRecvHolderDeschedule tid holder st hInv
        have D := applyRendezvousCallDonation H.invExt hD
        exact (H.trans D).trans (propagatePipChainCrossCore st2 recordedServer serverCore _
          D.invExt)
    · cases h
      have P := descheduleAtPlacement st holder hInv
      exact P.trans (propagatePipChainCrossCore _ recordedServer serverCore _ P.invExt)

/-- The receive leg's priority hand-off. -/
theorem applyReceiveLegPipHandoff (st : SystemState)
    (receiver dequeued alreadyWalked : SeLe4n.ThreadId) (executingCore : CoreId)
    (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.applyReceiveLegPipHandoff st receiver dequeued
      alreadyWalked executingCore) := by
  unfold _root_.SeLe4n.Kernel.applyReceiveLegPipHandoff
  split
  · exact refl hInv
  split
  · exact propagatePipChainCrossCore st receiver executingCore _ hInv
  · exact refl hInv

end RecordsFrame

/-! ### The state the receive leg runs on -/

/-- **What the receive leg reads, at the state it runs on**: the reply leg, the
donation pop and the reply leg's capability transfer keep every endpoint head
blocked, keep the server `.ready`, and add no endpoint.  The reply leg makes only
its target `.ready`, and neither the pop nor the transfer writes IPC state. -/
theorem replyRecvReceiveLegFacts {answer : Option Architecture.FaultReplyOutcome}
    {tid prevCaller : SeLe4n.ThreadId} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {rid : SeLe4n.ReplyId} {pre st st1 st1q st1p : SystemState}
    {sgi : Option (CoreId × Concurrency.SgiKind)}
    {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {xs : CapTransferSummary}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hR : _root_.SeLe4n.Kernel.endpointReplyOnCore tid prevCaller msg c st = (st1, .ok sgi))
    (hPop : _root_.SeLe4n.Kernel.replyRecvPopDonation rid prevCaller st1 = .ok (r, st1q))
    (hX : replyRecvReplyTransfer answer pre tid prevCaller grant st1q = .ok (xs, st1p))
    (hReady : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready) :
    queueHeadBlockedConsistent st1p ∧
      (∀ x, st1p.getTcb? tid = some x → x.ipcState = .ready) ∧
      (∀ (e : SeLe4n.ObjId) (ep : Endpoint), st1p.objects[e]? = some (.endpoint ep) →
        st.objects[e]? = some (.endpoint ep)) := by
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt tid prevCaller msg c st hInv
  have hQ1 := endpointReplyOnCore_preserves_queueHeadBlockedConsistent tid prevCaller msg c st
    hInv hQ (sgi? := sgi) (by rw [hR])
  have hEB := endpointReplyOnCore_endpoint_backward tid prevCaller msg c st hInv
  have hTB := endpointReplyOnCore_tcb_backward tid prevCaller msg c st hInv
  rw [hR] at hInv1 hQ1 hEB hTB
  obtain ⟨hQE, -, hQT⟩ := replyRecvPopDonation_frame hInv1 hPop
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX
  obtain ⟨hXE, -, hXT⟩ :=
    receiveTransferCaps_ipcFrame (RecordsFrame.replyRecvPopDonation hInv1 hPop).invExt hX
  have hPE : ∀ (e : SeLe4n.ObjId) (ep : Endpoint), st1p.objects[e]? = some (.endpoint ep) →
      st1.objects[e]? = some (.endpoint ep) := fun e ep h => hQE e ep (hXE e ep h)
  have hPT : ∀ (y : SeLe4n.ThreadId) (tcb' : TCB), st1p.objects[y.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st1.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState :=
    fun y t h => by
      obtain ⟨u, hu, hU⟩ := hXT y t h
      obtain ⟨v, hv, hV⟩ := hQT y u hu
      exact ⟨v, hv, hV.trans hU⟩
  refine ⟨queueHeadBlockedConsistent_of_endpoint_tcb_backward _ _ hPE hPT hQ1, fun x hx => ?_,
    fun e ep h => hEB e ep (hPE e ep h)⟩
  obtain ⟨y, hy, hS⟩ := hPT tid x ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)
  obtain ⟨z, hz, -, -, hZ⟩ := hTB tid y ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hy)
  rw [← hS]
  rcases hZ with hZ | ⟨hZ, -⟩
  · exact hZ
  · rw [hZ]; exact hReady z hz

namespace RecordsStep

/-- **The reply-receive keeps the address-space records and every fault record
parked**: the reply leg unparks its caller, every step after it keeps the
records, and the answer either finds the caller carrying no fault record or
clears the one it answers. -/
theorem endpointReplyRecvAnsweringOnCore {answer : Option Architecture.FaultReplyOutcome}
    {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState} {summary : CapTransferSummary}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hReady : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready)
    (hAns : answer = none → NoFaultAt st prevCaller)
    (h : _root_.SeLe4n.Kernel.endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg
      grant c st = .ok (summary, st')) :
    RecordsStep st st' := by
  unfold _root_.SeLe4n.Kernel.endpointReplyRecvAnsweringOnCore at h
  dsimp only at h
  have A := ReplyLegStep.endpointReplyOnCore (replier := tid) (target := prevCaller) (msg := msg)
    (c := c) hInv
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
  obtain ⟨hQp, hRp, -⟩ := replyRecvReceiveLegFacts hInv hQ hR hPop hX hReady
  have F0 := RecordsFrame.replyRecvPopDonation A.1.invExt hPop
  have F1 := F0.trans (RecordsFrame.receiveTransferCaps F0.invExt
    (by rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX; exact hX))
  have S2 := endpointReceiveDualWithCapsOnCore (endpointId := epId) (replyId := some rid)
    (c := c) F1.invExt hQp
    (fun x hx => by rw [hRp x hx]; exact ipcParked_ready)
  revert h S2
  generalize _root_.SeLe4n.Kernel.endpointReceiveDualWithCapsOnCore epId tid (some rid)
    c st1p = r2
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
  have Mid : RecordsStep st1 _ :=
    ((((RecordsStep.of_frame F1).trans S2).trans (.of_frame F3)).trans (.of_frame F4))
  cases answer with
  | none =>
    have F5 := RecordsFrame.stageDeliveredMessage _ prevCaller xs.capInfo F4.invExt
    exact (((A.2 (hAns rfl)).trans Mid).trans (.of_frame F5)).trans
      (.of_frame (RecordsFrame.stageWokenSendCompletion _ _ F5.invExt))
  | some o =>
    obtain ⟨S5, hN⟩ := faultReplyApplyOnCore _ prevCaller o F4.invExt
    have F6 := RecordsFrame.stageWokenSendCompletion _
      ((st1p.getEndpoint? epId).bind (·.sendQ.head)) S5.invExt
    exact ((A.1.trans (.of_step (Mid.trans S5))).trans (.of_step (.of_frame F6))).close
      (hN.frame F6)

end RecordsStep

namespace CallerReady

theorem ready {st : SystemState} {t : SeLe4n.ThreadId} (h : CallerReady st t) :
    ∀ x, st.getTcb? t = some x → x.ipcState = .ready := fun x hx => by
  obtain ⟨tcb, hT, hR⟩ := h
  have hE := hT.symm.trans ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)
  simp only [Option.some.injEq, KernelObject.tcb.injEq] at hE
  subst hE; exact hR

end CallerReady

open SeLe4n.Model.SystemState in
/-- **The reply-receive keeps the records**, its server the running thread: an
answer to a faulted caller clears its fault record, any other answer finds none. -/
theorem RecordsStage.endpointReplyRecvAnsweringOnCore
    {answer : Option Architecture.FaultReplyOutcome} {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState}
    {summary : CapTransferSummary} (hR : ipcReachable st) (hC : CallerReady st tid)
    (hAns : answer = none → NoFaultAt st prevCaller)
    (h : _root_.SeLe4n.Kernel.endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg
      grant c st = .ok (summary, st')) : RecordsStage st st' :=
  have hQ := hR.ipcInvariantFull.queueHeadBlockedConsistent
  RecordsStage.of_step (RecordsStep.endpointReplyRecvAnsweringOnCore hR.objects_invExt hQ hC.ready hAns h)
    fun hW => by
      have hOk := h
      unfold _root_.SeLe4n.Kernel.endpointReplyRecvAnsweringOnCore at hOk
      dsimp only at hOk
      cases hRl : _root_.SeLe4n.Kernel.endpointReplyOnCore tid prevCaller msg c st with
      | mk st1 res1 =>
      rw [hRl] at hOk
      cases res1 with
      | error _ => cases hOk
      | ok sgi =>
      dsimp only at hOk
      cases hP : _root_.SeLe4n.Kernel.replyRecvPopDonation rid prevCaller st1 with
      | error _ => rw [hP] at hOk; cases hOk
      | ok p =>
      obtain ⟨ret, st1q⟩ := p
      obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer st tid prevCaller grant st1q
      obtain ⟨hQp, hRp, hEp⟩ := replyRecvReceiveLegFacts hR.objects_invExt hQ hRl hP hX hC.ready
      have hPost : replyRecvReceiveLegState answer st tid grant rid prevCaller
          (_root_.SeLe4n.Kernel.endpointReplyOnCore tid prevCaller msg c st).1 = st1p := by
        rw [hRl]; exact replyRecvReceiveLegState_eq_of_ok _ _ _ _ _ _ _ _ _ _ _ hP hX
      refine endpointReplyRecvOnCore_preserves_replyWaitersConsistent epId tid rid prevCaller msg
        grant c st st' summary hR.objects_invExt hW ?_ ?_ h
      · rw [hPost]
        intro v hv
        obtain ⟨t, hT, rfl⟩ := tcb_of_replyViews hv
        have hS := hRp t ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hT)
        simp only [TCB.replyView, TCB.blockingServer?, hS]
      · rw [hPost]
        intro ep s hE hH
        refine ⟨fun hs => ?_, sendHead_serverFree hQp hE hH⟩
        subst hs
        obtain ⟨tcb, hT, hRd⟩ := hC
        rcases (hQ epId ep s tcb (hEp epId ep hE) hT).2 hH with hS | hS <;> rw [hRd] at hS <;>
          cases hS

/-- **The `.replyRecv` arm's transition keeps the records**: the answer the
caller's own fault record selects, so a caller answered with its message
carries no fault record. -/
theorem RecordsStage.replyRecvTransferOnCore {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage}
    {grant : Bool} {c : CoreId} {st st' : SystemState}
    {summary : CapTransferSummary} (hR : ipcReachable st) (hC : CallerReady st tid)
    (h : _root_.SeLe4n.Kernel.replyRecvTransferOnCore epId tid rid prevCaller label msg
      grant c st = .ok (summary, st')) : RecordsStage st st' := by
  unfold _root_.SeLe4n.Kernel.replyRecvTransferOnCore at h
  refine RecordsStage.endpointReplyRecvAnsweringOnCore hR hC (fun hA x hx => ?_) h
  cases hF : x.pendingFault with
  | none => rfl
  | some _ => simp only [replyRecvCallerFaultAnswer?, hx, hF] at hA; cases hA

end SeLe4n.Kernel
