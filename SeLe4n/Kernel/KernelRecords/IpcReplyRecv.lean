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

The composite theorems (`RecordsStep.endpointReplyRecvAnsweringOnCore`,
`RecordsStage.endpointReplyRecvAnsweringOnCore`,
`RecordsStage.replyRecvTransferOnCore`) live in `KernelRecords.Dispatch`, after
the return's frame: seL4-MCS `receiveIPC` runs `maybeReturnSchedContext` before
the receive leg (WS-SX SX8.2).
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
  · split at h
    · split at h
      · split at h
        · cases h
        · rename_i st1 hRet
          cases h
          have F := returnDonatedSchedContextResolved hInv hRet
          exact F.trans (settleReturnedContext _ _ _ F.invExt)
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
  · split at h
    · split at h
      · cases h
      · rename_i st2 hD
        cases h
        have D := applyRendezvousCallDonation hInv hD
        exact D.trans (propagatePipChainCrossCore st2 recordedServer serverCore _ D.invExt)
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

/-- **The caller's answer writes IPC state nowhere and adds no endpoint**: the
staged frame and the restart write the caller's TCB only, keeping its IPC
state; the abandon deschedules it first, which moves only run links. -/
theorem replyRecvAnswerCaller_ipcBackward (answer : Option Architecture.FaultReplyOutcome)
    (S : SystemState) (p : SeLe4n.ThreadId) (capInfo : Nat) (hInv : S.objects.invExt) :
    (∀ (e : SeLe4n.ObjId) (ep : Endpoint),
      (replyRecvAnswerCaller answer S p capInfo).objects[e]? = some (.endpoint ep) →
        S.objects[e]? = some (.endpoint ep)) ∧
    (∀ (y : SeLe4n.ThreadId) (tcb' : TCB),
      (replyRecvAnswerCaller answer S p capInfo).objects[y.toObjId]? = some (.tcb tcb') →
        ∃ tcb, S.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState) := by
  have upd : ∀ (X : SystemState) (f : TCB → TCB), X.objects.invExt →
      (∀ x, (f x).ipcState = x.ipcState) →
      (∀ (e : SeLe4n.ObjId) (ep : Endpoint), (X.updateTcb p f).objects[e]? = some (.endpoint ep) →
        X.objects[e]? = some (.endpoint ep)) ∧
      (∀ (y : SeLe4n.ThreadId) (tcb' : TCB), (X.updateTcb p f).objects[y.toObjId]? = some (.tcb tcb') →
        ∃ tcb, X.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState) := by
    intro X f hI hf
    refine ⟨fun e ep h => updateTcb_objects_back_nonTcb hI (fun _ h => by cases h) h,
      fun y t' h => ?_⟩
    obtain ⟨t, ht, hs⟩ := updateTcb_getTcb?_back hI hf
      ((SystemState.getTcb?_eq_some_iff _ _ _).mpr h)
    exact ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mp ht, hs⟩
  have refl : (∀ (e : SeLe4n.ObjId) (ep : Endpoint), S.objects[e]? = some (.endpoint ep) →
        S.objects[e]? = some (.endpoint ep)) ∧
      (∀ (y : SeLe4n.ThreadId) (tcb' : TCB), S.objects[y.toObjId]? = some (.tcb tcb') →
        ∃ tcb, S.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState) :=
    ⟨fun _ _ h => h, fun _ t h => ⟨t, h, rfl⟩⟩
  cases answer with
  | none =>
    show (∀ (e : SeLe4n.ObjId) (ep : Endpoint),
      (Architecture.stageDeliveredMessage S p capInfo).objects[e]? = some (.endpoint ep) →
        S.objects[e]? = some (.endpoint ep)) ∧
      (∀ (y : SeLe4n.ThreadId) (tcb' : TCB),
        (Architecture.stageDeliveredMessage S p capInfo).objects[y.toObjId]? = some (.tcb tcb') →
          ∃ tcb, S.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState)
    unfold Architecture.stageDeliveredMessage
    split
    · split
      · split
        · exact upd S _ hInv (fun _ => rfl)
        · exact refl
      · exact refl
    · exact refl
  | some o =>
    cases o with
    | restart frame => exact upd S _ hInv (fun _ => rfl)
    | abandon =>
      show (∀ (e : SeLe4n.ObjId) (ep : Endpoint),
        (faultAbandonOnCore S p (faultAbandonCore S p)).objects[e]? = some (.endpoint ep) →
          S.objects[e]? = some (.endpoint ep)) ∧
        (∀ (y : SeLe4n.ThreadId) (tcb' : TCB),
          (faultAbandonOnCore S p (faultAbandonCore S p)).objects[y.toObjId]? = some (.tcb tcb') →
            ∃ tcb, S.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState)
      unfold faultAbandonOnCore
      obtain ⟨hE, hT⟩ := upd (removeRunnableOnCore S p (faultAbandonCore S p))
        (fun tcb => { tcb.setPendingFault none with threadState := .Inactive })
        (removeRunnableOnCore_objects_invExt S p _ hInv) (fun _ => rfl)
      refine ⟨fun e ep h => removeRunnableOnCore_objects_back_nonTcb S p _
        (fun _ h => by cases h) (hE e ep h), fun y t' h => ?_⟩
      obtain ⟨u, hu, hU⟩ := hT y t' h
      obtain ⟨t0, h0, e0⟩ := removeRunnableOnCore_getTcb?_back S p (faultAbandonCore S p)
        ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hu)
      have hs : t0.ipcState = u.ipcState := by have := congrArg TCB.ipcState e0; exact this
      exact ⟨t0, (SystemState.getTcb?_eq_some_iff _ _ _).mp h0, hs.trans hU⟩

/-- **What the receive leg reads, at the answered state**: the caller's answer
keeps every endpoint head blocked, keeps the server `.ready`, and adds no
endpoint. -/
theorem replyRecvAnswerCaller_receiveLegFacts (answer : Option Architecture.FaultReplyOutcome)
    {S st : SystemState} (p tid : SeLe4n.ThreadId) (capInfo : Nat) (hInv : S.objects.invExt)
    (hQ : queueHeadBlockedConsistent S)
    (hReady : ∀ x, S.getTcb? tid = some x → x.ipcState = .ready)
    (hEp : ∀ (e : SeLe4n.ObjId) (ep : Endpoint), S.objects[e]? = some (.endpoint ep) →
      st.objects[e]? = some (.endpoint ep)) :
    queueHeadBlockedConsistent (replyRecvAnswerCaller answer S p capInfo) ∧
      (∀ x, (replyRecvAnswerCaller answer S p capInfo).getTcb? tid = some x →
        x.ipcState = .ready) ∧
      (∀ (e : SeLe4n.ObjId) (ep : Endpoint),
        (replyRecvAnswerCaller answer S p capInfo).objects[e]? = some (.endpoint ep) →
          st.objects[e]? = some (.endpoint ep)) := by
  obtain ⟨hE, hT⟩ := replyRecvAnswerCaller_ipcBackward answer S p capInfo hInv
  refine ⟨queueHeadBlockedConsistent_of_endpoint_tcb_backward _ _ hE hT hQ, fun x hx => ?_,
    fun e ep h => hEp e ep (hE e ep h)⟩
  obtain ⟨y, hy, hS⟩ := hT tid x ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)
  rw [← hS]; exact hReady y ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hy)

end SeLe4n.Kernel
