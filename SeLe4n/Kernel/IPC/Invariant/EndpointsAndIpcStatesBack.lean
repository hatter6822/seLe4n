-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecv
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Ipc

/-!
# Endpoints and IPC states, read backward

WS-SX SX36.1.  `EndpointsAndIpcStatesBack st st'`: every endpoint of `st'` is
one of `st`'s, and every thread of `st'` was a thread of `st` with the same IPC
state.  It is reflexive and transitive, it carries `queueHeadBlockedConsistent`
and a thread's `.ready` forward, and every step of a reply after its reply leg
keeps it: the donation return, the priority-inheritance walk, the capability
transfer, the caller's answer and the nothing-received outcome.  So a reply
whose receive capability is refused after it leaves a state the capability
fault's delivery can read.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

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

/-- **Two states agree on every endpoint and every thread's IPC state,
read backward**: every endpoint of the later state is one of the earlier's,
and every thread of the later state was a thread of the earlier one with the
same IPC state. -/
def EndpointsAndIpcStatesBack (st st' : SystemState) : Prop :=
  (∀ (e : SeLe4n.ObjId) (ep : Endpoint), st'.objects[e]? = some (.endpoint ep) →
    st.objects[e]? = some (.endpoint ep)) ∧
  (∀ (y : SeLe4n.ThreadId) (tcb' : TCB), st'.objects[y.toObjId]? = some (.tcb tcb') →
    ∃ tcb, st.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState)

namespace EndpointsAndIpcStatesBack

theorem refl (st : SystemState) : EndpointsAndIpcStatesBack st st :=
  ⟨fun _ _ h => h, fun _ t h => ⟨t, h, rfl⟩⟩

theorem trans {a b c : SystemState} (h1 : EndpointsAndIpcStatesBack a b)
    (h2 : EndpointsAndIpcStatesBack b c) : EndpointsAndIpcStatesBack a c :=
  ⟨fun e ep h => h1.1 e ep (h2.1 e ep h), fun y t h => by
    obtain ⟨u, hu, hU⟩ := h2.2 y t h
    obtain ⟨v, hv, hV⟩ := h1.2 y u hu
    exact ⟨v, hv, hV.trans hU⟩⟩

theorem queueHeadBlocked {st st' : SystemState} (h : EndpointsAndIpcStatesBack st st')
    (hQ : queueHeadBlockedConsistent st) : queueHeadBlockedConsistent st' :=
  queueHeadBlockedConsistent_of_endpoint_tcb_backward _ _ h.1 h.2 hQ

theorem ready {st st' : SystemState} (h : EndpointsAndIpcStatesBack st st')
    {t : SeLe4n.ThreadId} (hR : ∀ x, st.getTcb? t = some x → x.ipcState = .ready) :
    ∀ x, st'.getTcb? t = some x → x.ipcState = .ready := fun x hx => by
  obtain ⟨y, hy, hS⟩ := h.2 t x ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)
  rw [← hS]; exact hR y ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hy)

end EndpointsAndIpcStatesBack

/-- The reply's donation return writes no endpoint and no IPC state. -/
theorem applyReplyDonationOnCore_endpointsAndIpcStatesBack {st st' : SystemState}
    {rid : SeLe4n.ReplyId} {v : SeLe4n.ValidThreadId} {home : CoreId} {keep : Bool} {ec : CoreId}
    (hInv : st.objects.invExt) (h : applyReplyDonationOnCore st rid v home keep ec = .ok st') :
    EndpointsAndIpcStatesBack st st' := by
  refine ⟨fun k ep hk => ?_, fun y t hT =>
    applyReplyDonationOnCore_tcb_ipcState_backward st st' rid v home hInv h y.toObjId t hT⟩
  rcases applyReplyDonationOnCore_ok_decompose st st' rid v home h with ⟨_, hPop⟩ | _
  · exact (popUnheldReplyHead_frame hInv hPop).1 k ep hk
  rcases applyReplyDonationOnCore_objects_frame st st' rid v home h with
    ⟨_, hObj⟩ | ⟨scId, n, s1, _, _, _, hP, hObj⟩ | ⟨scId, holder, n, s1, hRet, hObj⟩ |
      ⟨_, _, -, -, -, hS⟩ | ⟨_, _, _, -, -, hK⟩
  · rw [hObj] at hk; exact hk
  · exact returnUnheldSchedContext_endpoint_backward hInv hP k ep (hObj.get_endpoint_iff.mp hk)
  · exact returnDonatedSchedContext_endpoint_backward st s1 holder scId v.val hInv n hRet k ep
      (hObj.get_endpoint_iff.mp hk)
  · exact severUnheldSchedContext_endpoint_backward hInv hS k ep hk
  · exact keepDonatedSchedContext_endpoint_backward hInv hK k ep hk

/-- The priority-inheritance walk writes no endpoint and no IPC state. -/
theorem propagatePipChainCrossCore_endpointsAndIpcStatesBack (st : SystemState)
    (t : SeLe4n.ThreadId) (c : CoreId) (fuel : Nat) (hInv : st.objects.invExt) :
    EndpointsAndIpcStatesBack st (PriorityInheritance.propagatePipChainCrossCore st t c fuel).1 := by
  refine ⟨fun k ep hk => ?_, fun y x hT =>
    PriorityInheritance.propagatePipChainCrossCore_tcb_ipcState_backward st t c fuel hInv y x hT⟩
  rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st t c hInv k with
    hE | ⟨pre, post, -, hPost, -⟩
  · rw [← hE]; exact hk
  · rw [hPost] at hk; cases hk

/-- **A whole cross-core reply keeps the endpoint heads blocked and keeps
every `.ready` thread `.ready`**: the reply leg makes only its target `.ready`
(`endpointReplyOnCore_preserves_queueHeadBlockedConsistent`), and the donation
return and the priority-inheritance reversion write no endpoint and no IPC
state. -/
theorem endpointReplyCrossCoreDispatch_receiveLegFacts {replier target t : SeLe4n.ThreadId}
    {keep : Bool}
    {msg : IpcMessage} {c : CoreId} {st st' : SystemState}
    {sgi : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hReady : ∀ x, st.getTcb? t = some x → x.ipcState = .ready)
    (h : endpointReplyCrossCoreDispatch replier target msg c st keep = (st', .ok sgi)) :
    queueHeadBlockedConsistent st' ∧ (∀ x, st'.getTcb? t = some x → x.ipcState = .ready) := by
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt replier target msg c st hInv
  have hTB := endpointReplyOnCore_tcb_backward replier target msg c st hInv
  unfold endpointReplyCrossCoreDispatch at h
  cases hR : endpointReplyOnCore replier target msg c st with
  | mk st1 r =>
    rw [hR] at h hInv1 hTB
    cases r with
    | error e => cases h
    | ok s0 =>
      have hQ1 := endpointReplyOnCore_preserves_queueHeadBlockedConsistent replier target msg c st
        hInv hQ (sgi? := s0) (by rw [hR])
      rw [hR] at hQ1
      have hR1 : ∀ x, st1.getTcb? t = some x → x.ipcState = .ready := fun x hx => by
        obtain ⟨z, hz, -, -, hZ⟩ := hTB t x hx
        rcases hZ with hZ | ⟨hZ, -⟩
        · exact hZ
        · rw [hZ]; exact hReady z hz
      suffices B : EndpointsAndIpcStatesBack st1 st' from ⟨B.queueHeadBlocked hQ1, B.ready hR1⟩
      dsimp only at h
      repeat' split at h
      all_goals first
        | (cases h; done)
        | (cases h; exact EndpointsAndIpcStatesBack.refl _)
        | (cases h; exact propagatePipChainCrossCore_endpointsAndIpcStatesBack _ _ _ _ hInv1)
        | (rename_i st2 hD
           cases h
           exact (applyReplyDonationOnCore_endpointsAndIpcStatesBack hInv1 hD).trans
             (propagatePipChainCrossCore_endpointsAndIpcStatesBack _ _ _ _
               (applyReplyDonationOnCore_preserves_objects_invExt _ _ _ _ _ hInv1 hD)))
        | (rename_i st2 hD
           cases h
           exact applyReplyDonationOnCore_endpointsAndIpcStatesBack hInv1 hD)

/-- **A checked reply transfer keeps the endpoint heads blocked and keeps every
`.ready` thread `.ready`** (WS-SX SX36.1), on both branches: the fault reply is
the whole reply with the empty message then the answer
(`replyRecvAnswerCaller_ipcBackward`), and the ordinary reply is the whole
reply, its capability transfer (`receiveTransferCaps_ipcFrame`) and the staged
frame. -/
theorem replyTransferOnCoreChecked_receiveLegFacts {ctx : LabelingContext}
    {replier prev t : SeLe4n.ThreadId} {mi : MessageInfo} {regs : Array SeLe4n.RegValue}
    {msg : IpcMessage} {grant : Bool} {c : CoreId} {st st' : SystemState} {keep : Bool}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hReady : ∀ x, st.getTcb? t = some x → x.ipcState = .ready)
    (h : replyTransferOnCoreChecked ctx replier prev mi regs msg grant c st keep = .ok ((), st')) :
    queueHeadBlockedConsistent st' ∧ (∀ x, st'.getTcb? t = some x → x.ipcState = .ready) := by
  unfold replyTransferOnCoreChecked at h
  split at h
  · cases hF : faultReplyOnCore replier prev mi regs c st keep with
    | mk s r =>
      rw [hF] at h
      cases r with
      | error e => cases h
      | ok y =>
        cases h
        unfold faultReplyOnCore at hF
        split at hF
        · cases hF
        split at hF
        · cases hF
        cases hD : endpointReplyCrossCoreDispatch replier prev IpcMessage.empty c st keep with
        | mk st1 r =>
          rw [hD] at hF
          cases r with
          | error e => cases hF
          | ok sgi =>
            cases hF
            obtain ⟨hQ1, hR1⟩ := endpointReplyCrossCoreDispatch_receiveLegFacts hInv hQ hReady hD
            have hI1 := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier prev
              IpcMessage.empty c st hInv keep
            rw [hD] at hI1
            obtain ⟨hE, hT⟩ := replyRecvAnswerCaller_ipcBackward
              (some (Architecture.decodeFaultReply _ _ mi regs)) st1 prev 0 hI1
            have B : EndpointsAndIpcStatesBack st1 _ := ⟨hE, hT⟩
            exact ⟨B.queueHeadBlocked hQ1, B.ready hR1⟩
  · cases hC : endpointReplyCrossCoreDispatchChecked ctx replier prev msg c st keep with
    | mk st1 r =>
      rw [hC] at h
      cases r with
      | error e => cases h
      | ok sgi =>
        have hD : endpointReplyCrossCoreDispatch replier prev msg c st keep = (st1, .ok sgi) := by
          unfold endpointReplyCrossCoreDispatchChecked at hC
          split at hC
          · exact hC
          · cases hC
        try dsimp only at h
        cases hX : replyTransferCaps st replier prev grant st1 with
        | error e => rw [hX] at h; cases h
        | ok p =>
          obtain ⟨xs, st2⟩ := p
          rw [hX] at h
          cases h
          obtain ⟨hQ1, hR1⟩ := endpointReplyCrossCoreDispatch_receiveLegFacts hInv hQ hReady hD
          have hI1 := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier prev msg c st
            hInv keep
          rw [hD] at hI1
          unfold replyTransferCaps at hX
          obtain ⟨hXE, -, hXT⟩ := receiveTransferCaps_ipcFrame hI1 hX
          obtain ⟨hE, hT⟩ := replyRecvAnswerCaller_ipcBackward none st2 prev xs.capInfo
            (receiveTransferCaps_objects_invExt hI1 hX)
          have B : EndpointsAndIpcStatesBack st1 _ := (show EndpointsAndIpcStatesBack st1 st2 from
            ⟨hXE, hXT⟩).trans ⟨hE, hT⟩
          exact ⟨B.queueHeadBlocked hQ1, B.ready hR1⟩


/-- **A whole cross-core reply adds no endpoint**: the reply leg writes none
(`endpointReplyOnCore_endpoint_backward`), and the donation return and the
priority-inheritance reversion write no endpoint. -/
theorem endpointReplyCrossCoreDispatch_endpoint_backward {replier target : SeLe4n.ThreadId}
    {keep : Bool} {msg : IpcMessage} {c : CoreId} {st st' : SystemState}
    {sgi : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : endpointReplyCrossCoreDispatch replier target msg c st keep = (st', .ok sgi)) :
    ∀ (e : SeLe4n.ObjId) (ep : Endpoint), st'.objects[e]? = some (.endpoint ep) →
      st.objects[e]? = some (.endpoint ep) := by
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt replier target msg c st hInv
  have hEB := endpointReplyOnCore_endpoint_backward replier target msg c st hInv
  unfold endpointReplyCrossCoreDispatch at h
  cases hR : endpointReplyOnCore replier target msg c st with
  | mk st1 r =>
    rw [hR] at h hInv1 hEB
    cases r with
    | error e => cases h
    | ok s0 =>
      suffices B : EndpointsAndIpcStatesBack st1 st' from fun e ep he => hEB e ep (B.1 e ep he)
      dsimp only at h
      repeat' split at h
      all_goals first
        | (cases h; done)
        | (cases h; exact EndpointsAndIpcStatesBack.refl _)
        | (cases h; exact propagatePipChainCrossCore_endpointsAndIpcStatesBack _ _ _ _ hInv1)
        | (rename_i st2 hD
           cases h
           exact (applyReplyDonationOnCore_endpointsAndIpcStatesBack hInv1 hD).trans
             (propagatePipChainCrossCore_endpointsAndIpcStatesBack _ _ _ _
               (applyReplyDonationOnCore_preserves_objects_invExt _ _ _ _ _ hInv1 hD)))
        | (rename_i st2 hD
           cases h
           exact applyReplyDonationOnCore_endpointsAndIpcStatesBack hInv1 hD)

/-- **A checked reply transfer adds no endpoint**, on both branches: the whole
reply, then the answer, or the capability transfer and the staged frame. -/
theorem replyTransferOnCoreChecked_endpoint_backward {ctx : LabelingContext}
    {replier prev : SeLe4n.ThreadId} {mi : MessageInfo} {regs : Array SeLe4n.RegValue}
    {msg : IpcMessage} {grant : Bool} {c : CoreId} {st st' : SystemState} {keep : Bool}
    (hInv : st.objects.invExt)
    (h : replyTransferOnCoreChecked ctx replier prev mi regs msg grant c st keep = .ok ((), st')) :
    ∀ (e : SeLe4n.ObjId) (ep : Endpoint), st'.objects[e]? = some (.endpoint ep) →
      st.objects[e]? = some (.endpoint ep) := by
  unfold replyTransferOnCoreChecked at h
  split at h
  · cases hF : faultReplyOnCore replier prev mi regs c st keep with
    | mk s r =>
      rw [hF] at h
      cases r with
      | error e => cases h
      | ok y =>
        cases h
        unfold faultReplyOnCore at hF
        split at hF
        · cases hF
        split at hF
        · cases hF
        cases hD : endpointReplyCrossCoreDispatch replier prev IpcMessage.empty c st keep with
        | mk st1 r =>
          rw [hD] at hF
          cases r with
          | error e => cases hF
          | ok sgi =>
            cases hF
            have hB1 := endpointReplyCrossCoreDispatch_endpoint_backward hInv hD
            have hI1 := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier prev
              IpcMessage.empty c st hInv keep
            rw [hD] at hI1
            obtain ⟨hE, -⟩ := replyRecvAnswerCaller_ipcBackward
              (some (Architecture.decodeFaultReply _ _ mi regs)) st1 prev 0 hI1
            exact fun e ep he => hB1 e ep (hE e ep he)
  · cases hC : endpointReplyCrossCoreDispatchChecked ctx replier prev msg c st keep with
    | mk st1 r =>
      rw [hC] at h
      cases r with
      | error e => cases h
      | ok sgi =>
        have hD : endpointReplyCrossCoreDispatch replier prev msg c st keep = (st1, .ok sgi) := by
          unfold endpointReplyCrossCoreDispatchChecked at hC
          split at hC
          · exact hC
          · cases hC
        try dsimp only at h
        cases hX : replyTransferCaps st replier prev grant st1 with
        | error e => rw [hX] at h; cases h
        | ok p =>
          obtain ⟨xs, st2⟩ := p
          rw [hX] at h
          cases h
          have hB1 := endpointReplyCrossCoreDispatch_endpoint_backward hInv hD
          have hI1 := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier prev msg c st
            hInv keep
          rw [hD] at hI1
          unfold replyTransferCaps at hX
          obtain ⟨hXE, -, -⟩ := receiveTransferCaps_ipcFrame hI1 hX
          obtain ⟨hE, -⟩ := replyRecvAnswerCaller_ipcBackward none st2 prev xs.capInfo
            (receiveTransferCaps_objects_invExt hI1 hX)
          exact fun e ep he => hB1 e ep (hXE e ep (hE e ep he))

/-- A step that moves only run-queue links writes no endpoint and no IPC state. -/
theorem EndpointsAndIpcStatesBack.of_objectsAgreeOffRunLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffRunLinks st) : EndpointsAndIpcStatesBack st st' :=
  ⟨fun _ _ hk => h.get_endpoint_iff.mp hk, fun _ _ hT => by
    obtain ⟨u, hu, hE⟩ := h.get_tcb' hT
    exact ⟨u, hu, by
      first
        | exact (TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hE).symm
        | exact TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hE⟩⟩

/-- **The nothing-received outcome writes no endpoint and no IPC state**: the
holder's deschedule keeping the current slot moves only run-queue links, and the
priority-inheritance walk writes neither. -/
theorem replyRecvNothingReceived_endpointsAndIpcStatesBack (rs : SeLe4n.ThreadId) (c : CoreId)
    (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (S : SystemState)
    (hInv : S.objects.invExt) :
    EndpointsAndIpcStatesBack S (replyRecvNothingReceived rs c ret? S) := by
  unfold replyRecvNothingReceived
  cases ret? with
  | none => exact propagatePipChainCrossCore_endpointsAndIpcStatesBack _ _ _ _ hInv
  | some p =>
    obtain ⟨_, holder⟩ := p
    dsimp only
    have hD := descheduleKeepingCurrentOnCore_induct (fun a b => EndpointsAndIpcStatesBack a b)
      S holder c (.refl _)
      (.of_objectsAgreeOffRunLinks (descheduleAtPlacement_objectsAgreeOffRunLinks _ _))
    have hI := descheduleKeepingCurrentOnCore_induct (fun _ b => b.objects.invExt)
      S holder c hInv (descheduleAtPlacement_preserves_objects_invExt _ _ hInv)
    exact hD.trans (propagatePipChainCrossCore_endpointsAndIpcStatesBack _ _ _ _ hI)

/-- **The nothing-received state after a reply holds only endpoints of the
entry state** (WS-SX SX36.1): the reply leg, the pop, the reply's transfer, the
caller's answer and the nothing-received outcome write no endpoint but the
reply leg's, read backward. -/
theorem replyRecvNothingReceivedAfterReply_endpoint_backward
    {answer : Option Architecture.FaultReplyOutcome} {t prev rs : SeLe4n.ThreadId}
    {msg : IpcMessage} {grant : Bool} {c : CoreId} {rid : SeLe4n.ReplyId}
    {st st1 popped st1p : SystemState} {sgi : Option (CoreId × Concurrency.SgiKind)}
    {ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {xs : CapTransferSummary}
    (hInv : st.objects.invExt)
    (hR : endpointReplyOnCore t prev msg c st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation rid prev st1 = .ok (ret?, popped))
    (hX : replyRecvReplyTransfer answer st t prev grant popped = .ok (xs, st1p)) :
    ∀ (e : SeLe4n.ObjId) (ep : Endpoint),
      (replyRecvNothingReceived rs c ret?
          (replyRecvAnswerCaller answer st1p prev xs.capInfo)).objects[e]? =
        some (.endpoint ep) →
      st.objects[e]? = some (.endpoint ep) := by
  have hI1 := endpointReplyOnCore_preserves_objects_invExt t prev msg c st hInv
  have hEB := endpointReplyOnCore_endpoint_backward t prev msg c st hInv
  rw [hR] at hI1 hEB
  have hI2 := replyRecvPopDonation_preserves_objects_invExt rid prev st1 popped ret? hI1 hPop
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX
  have hIp := receiveTransferCaps_objects_invExt hI2 hX
  have hIa := replyRecvAnswerCaller_preserves_objects_invExt answer st1p prev xs.capInfo hIp
  obtain ⟨hPE, -, hPT⟩ := replyRecvPopDonation_frame hI1 hPop
  obtain ⟨hXE, -, hXT⟩ := receiveTransferCaps_ipcFrame hI2 hX
  obtain ⟨hE, hT⟩ := replyRecvAnswerCaller_ipcBackward answer st1p prev xs.capInfo hIp
  have B := ((show EndpointsAndIpcStatesBack st1 popped from ⟨hPE, hPT⟩).trans
    (show EndpointsAndIpcStatesBack popped st1p from ⟨hXE, hXT⟩)).trans
    ((show EndpointsAndIpcStatesBack st1p _ from ⟨hE, hT⟩).trans
      (replyRecvNothingReceived_endpointsAndIpcStatesBack rs c ret? _ hIa))
  exact fun e ep he => hEB e ep (B.1 e ep he)

end SeLe4n.Kernel
