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
the post-receive donation, the receive leg's priority hand-off and the two
stagers.  Every step between the legs writes scheduling contexts, run queues and
the scheduler only, so each is a records frame.
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

/-- **What the receive leg reads, at the state it runs on**: the reply leg and the
donation pop keep every endpoint head blocked, keep the server `.ready`, and add
no endpoint.  The reply leg makes only its target `.ready`, and the pop writes
no IPC state. -/
theorem replyRecvReceiveLegFacts {tid prevCaller : SeLe4n.ThreadId} {msg : IpcMessage}
    {c : CoreId} {rid : SeLe4n.ReplyId} {st st1 st1p : SystemState}
    {sgi : Option (CoreId × Concurrency.SgiKind)}
    {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hR : _root_.SeLe4n.Kernel.endpointReplyOnCore tid prevCaller msg c st = (st1, .ok sgi))
    (hPop : _root_.SeLe4n.Kernel.replyRecvPopDonation rid prevCaller st1 = .ok (r, st1p))
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
  obtain ⟨hPE, -, hPT⟩ := replyRecvPopDonation_frame hInv1 hPop
  refine ⟨queueHeadBlockedConsistent_of_endpoint_tcb_backward _ _ hPE hPT hQ1, fun x hx => ?_,
    fun e ep h => hEB e ep (hPE e ep h)⟩
  obtain ⟨y, hy, hS⟩ := hPT tid x ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)
  obtain ⟨z, hz, -, -, hZ⟩ := hTB tid y ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hy)
  rw [← hS]
  rcases hZ with hZ | ⟨hZ, -⟩
  · exact hZ
  · rw [hZ]; exact hReady z hz

end SeLe4n.Kernel
