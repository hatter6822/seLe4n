-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.SignalDonationFrame
import SeLe4n.Kernel.IPC.Invariant.ReplySignalFrame
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SuspendHolders

/-!
# The binding pair across a reply

seL4-MCS's `ReplyRecv` runs the reply first and the receive second; when the
receive completes its bound notification, `completeSignal`'s
`maybeDonateSchedContext` runs on the state the reply left.  The donation's
family lemmas ask the binding pair there (`schedContextBindingBidirectional`).

The reply moves bindings on one arm only: a donated context returned to its
caller (`returnDonatedSchedContext`), or an unheld one popped back to its owner
(`returnUnheldSchedContext`).  Every other leg — the delivery store, the run
and release links, the priority-inheritance revert, the capability transfer
and the delivered message's frame — keeps the context every thread names and
the thread every context names (`scIdLinksAgree`).  The return arms need the
pair's other half too (`holdersNameTheirContexts`: a context's bound thread
names it back), so the pair carried is both halves
(`schedContextBindingPair`).
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **The binding pair, both halves**: a thread's context names it, and a
context's thread names it, each read through the context a binding names. -/
def schedContextBindingPair (st : SystemState) : Prop :=
  schedContextBindingBidirectional st ∧ holdersNameTheirContexts st

theorem schedContextBindingPair_of_consistent {st : SystemState}
    (hC : schedContextBindingConsistent st) (hD : donationOwnerValid st) :
    schedContextBindingPair st :=
  ⟨schedContextBindingBidirectional_of_consistent hC hD,
    holdersNameTheirContexts_of_schedContextBindingConsistent hC⟩

namespace schedContextBindingPair

theorem of_scIdLinksAgree {st st' : SystemState} (hA : scIdLinksAgree st st')
    (h : schedContextBindingPair st) : schedContextBindingPair st' := by
  refine ⟨schedContextBindingBidirectional.of_scIdLinksAgree hA h.1,
    holdersNameTheirContexts.of_back (fun s sc' hs => ?_) (fun t x' hx => ?_) h.2⟩
  · have e := hA.2 s
    rw [hs] at e
    obtain ⟨sc, hsc, esc⟩ := Option.map_eq_some_iff.mp e.symm
    exact ⟨sc, hsc, esc⟩
  · have e := hA.1 t
    rw [hx] at e
    obtain ⟨x, hx0, ex⟩ := Option.map_eq_some_iff.mp e.symm
    exact ⟨x, hx0, ex⟩

theorem of_bindingLinksAgree {st st' : SystemState} (hB : bindingLinksAgree st st')
    (h : schedContextBindingPair st) : schedContextBindingPair st' :=
  of_scIdLinksAgree (scIdLinksAgree.of_bindingLinksAgree hB) h

theorem of_schedLinkFrame {st st' : SystemState} (hF : SchedLinkFrame st st')
    (h : schedContextBindingPair st) : schedContextBindingPair st' :=
  of_bindingLinksAgree hF.binding h

end schedContextBindingPair

namespace bindingLinksAgree

theorem of_offRunLinks {st st' : SystemState} (h : st'.objectsAgreeOffRunLinks st) :
    bindingLinksAgree st st' :=
  fun o => proj_eq_of_map_eq _ _ schedBindingLinksOf_withoutRunLinks (h o)

theorem of_offSchedulerLinks {st st' : SystemState} (h : st'.objectsAgreeOffSchedulerLinks st) :
    bindingLinksAgree st st' :=
  fun o => proj_eq_of_map_eq _ _ (fun x => by cases x <;> rfl) (h o)

end bindingLinksAgree

/-- **The donated context's return keeps the binding pair**: the returned
context goes to the recipient, whose binding the return writes to name it; the
holder's binding is cleared; a thread the step leaves alone held no binding to
the returned context, since that context named the holder. -/
theorem returnDonatedSchedContext_bindingPair {st st' : SystemState}
    {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {originalOwner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt) (hP : schedContextBindingPair st)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    schedContextBindingPair st' := by
  refine ⟨?_, returnDonatedSchedContext_holdersNameTheirContexts hObjInv hP.2 h⟩
  obtain ⟨scPre, hScPre, hScPreBound⟩ :=
    returnDonatedSchedContext_ok_implies_sc_bound st st' serverTid scId originalOwner
      newOwner? h
  obtain ⟨scPost, hScPost, hScPostBound⟩ :=
    returnDonatedSchedContext_post_boundThread st st' serverTid scId originalOwner hObjInv
      newOwner? h
  intro y x' s hx' hs
  have hC := returnDonatedSchedContext_tcb_binding_cases st st' serverTid scId originalOwner
    newOwner? hObjInv h y.toObjId x' hx'
  by_cases hKS : y.toObjId = serverTid.toObjId
  · rw [hC.1 hKS] at hs; cases hs
  by_cases hKO : y.toObjId = originalOwner.toObjId
  · rw [hC.2.1 hKS hKO, donationReturnBinding_scId?] at hs
    cases hs
    have e := SeLe4n.ThreadId.toObjId_injective _ _ hKO
    subst e
    exact ⟨scPost, (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hScPost, hScPostBound⟩
  · obtain ⟨u, hu, hub⟩ := hC.2.2 hKS hKO
    obtain ⟨sc0, h0, hbt⟩ := hP.1 y u s hu (by rw [hub]; exact hs)
    by_cases hSS : s = scId
    · subst hSS
      rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp hScPre] at h0
      cases h0
      rw [hScPreBound] at hbt
      cases hbt
      exact absurd rfl hKS
    · have e := returnDonatedSchedContext_getSchedContext?_ne st st' serverTid scId s
        originalOwner hSS hObjInv newOwner? h
      refine ⟨sc0, (SystemState.getSchedContext?_eq_some_iff _ _ _).mp ?_, hbt⟩
      rw [e]; exact (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr h0

/-- **An unheld context's pop keeps the binding pair**: the context, bound to
no thread, goes to the recipient, unbound before, whose binding the pop writes
to name it; every other thread and context is as it was. -/
theorem returnUnheldSchedContext_bindingPair {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt) (hP : schedContextBindingPair st)
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    schedContextBindingPair st' := by
  obtain ⟨sc, head?, ot, hSc, hB0, -, hRcp, hO, hNR, hSc', hO', tBwd, -, cBwd, cFwd⟩ :=
    returnUnheldSchedContext_objects hObjInv h
  have hUnheld : ∀ t, sc.boundThread ≠ some t := by
    intro t e; unfold SchedContext.boundThread at e; rw [hB0] at e; cases e
  have hOwnU : ot.schedContextBinding = .unbound := by
    have e := donationRecipientAcceptable_eq_of_some st owner ot
      (lookupTcb_of_objects_of_not_reserved st owner ot hO hNR)
    rw [hRcp] at e
    revert e; cases ot.schedContextBinding <;> simp [BEq.beq]
  have hPostBt : (donationReturnSchedContext sc owner (head?.bind (fun p => p.2.prev))
      newOwner?).boundThread = some owner := by
    unfold SchedContext.boundThread donationReturnSchedContext
    simp only [SeLe4n.ThreadId.optCode, SeLe4n.ThreadId.ofOptCode]
  refine ⟨fun y x' s hx' hs => ?_, fun s sc' t hs hb x hx => ?_⟩
  · by_cases hKO : y.toObjId = owner.toObjId
    · have e := SeLe4n.ThreadId.toObjId_injective _ _ hKO
      subst e
      rw [hO'] at hx'; cases hx'
      rw [donationReturnBinding_stored, donationReturnBinding_scId?] at hs
      cases hs
      exact ⟨_, hSc', hPostBt⟩
    · obtain ⟨sc0, h0, hbt⟩ := hP.1 y x' s (tBwd _ _ hKO hx') hs
      by_cases hSS : s.toObjId = scId.toObjId
      · rw [hSS, hSc] at h0; cases h0; exact absurd hbt (hUnheld y)
      · exact ⟨sc0, cFwd _ _ hSS h0, hbt⟩
  · have hs' := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hs
    have hx' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hx
    by_cases hSS : s.toObjId = scId.toObjId
    · have e := SeLe4n.SchedContextId.toObjId_injective _ _ hSS
      subst e
      rw [hSc'] at hs'; cases hs'
      rw [hPostBt] at hb; cases hb
      rw [hO'] at hx'; cases hx'
      rw [donationReturnBinding_stored, donationReturnBinding_scId?]
    · have h0 := cBwd _ _ hSS hs'
      have hpre := hP.2 s sc' t ((SystemState.getSchedContext?_eq_some_iff _ _ _).mpr h0) hb
      by_cases hKO : t.toObjId = owner.toObjId
      · have e := SeLe4n.ThreadId.toObjId_injective _ _ hKO
        subst e
        have := hpre ot ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hO)
        rw [hOwnU] at this; cases this
      · exact hpre x ((SystemState.getTcb?_eq_some_iff _ _ _).mpr (tBwd _ _ hKO hx'))

/-- A TCB's IPC state and message written keep every scheduling link. -/
theorem SchedLinkFrame.storeTcbIpcStateAndMessage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {ipc : ThreadIpcState} {msg : Option IpcMessage} (hInv : st.objects.invExt)
    (h : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') : SchedLinkFrame st st' := by
  unfold SeLe4n.Kernel.storeTcbIpcStateAndMessage at h
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  have hPre := lookupTcb_some_objects st tid tcb hL
  exact SchedLinkFrame.storeObject hInv hS (by rw [hPre]; rfl) (by rw [hPre]; rfl)
    (by rw [hPre]; rfl)

/-- The caller's reply frame removed: the splice, then the consume. -/
theorem SchedLinkFrame.removeCallerReplyFrame {st st' : SystemState} {c : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.removeCallerReplyFrame c rid st = .ok ((), st')) : SchedLinkFrame st st' :=
  (SchedLinkFrame.cutReplyFrameOutOrSelf st rid hInv).trans
    (SchedLinkFrame.consumeCallerReply (cutReplyFrameOutOrSelf_preserves_objects_invExt st rid hInv) h)

/-- **The single-core reply keeps every binding link**: the delivery store, a
link-only wake and the reply-frame removal. -/
theorem endpointReply_bindingLinksAgree
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    bindingLinksAgree st st' := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      split at hStep
      · cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
        | error e => simp [hMsg] at hStep
        | ok st'' =>
          simp only [hMsg] at hStep
          have h2 : bindingLinksAgree st (ensureRunnable st'' target) :=
            bindingLinksAgree.trans (SchedLinkFrame.storeTcbIpcStateAndMessage hObjInv hMsg).binding
              (bindingLinksAgree.of_offRunLinks (ensureRunnable_objectsAgreeOffRunLinks st'' target))
          have hObjInvMid : (ensureRunnable st'' target).objects.invExt := by
            apply ensureRunnable_objects_invExt
            exact storeTcbIpcStateAndMessage_preserves_objects_invExt st st'' target .ready
              (some msg) hObjInv hMsg
          cases hRO : tcb.replyObject with
          | none =>
            simp only [hRO, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
            rw [← hStep]
            exact h2.trans (bindingLinksAgree.of_offRunLinks
              (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ _ _))
          | some rid =>
            simp only [hRO] at hStep
            obtain ⟨st2, hRm, rfl⟩ := removeCallerReplyFrame_unlink_ok hStep
            exact (h2.trans (SchedLinkFrame.removeCallerReplyFrame hObjInvMid hRm).binding).trans
              (bindingLinksAgree.of_offRunLinks
                (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ _ _))
      · simp at hStep

/-- The cross-core reply leg: the single-core reply, with objects agreeing off
the scheduler links. -/
theorem endpointReplyOnCore_bindingLinksAgree
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    bindingLinksAgree st (endpointReplyOnCore replier target msg c st).1 := by
  rcases endpointReplyOnCore_post_agrees replier target msg c st hObjInv with
    hEq | ⟨expected, r1, hR, hA⟩
  · exact bindingLinksAgree.of_objects_eq (by rw [hEq])
  · exact (endpointReply_bindingLinksAgree st r1 expected target msg hObjInv hR).trans
      (bindingLinksAgree.of_offSchedulerLinks hA.objects)

/-- **The donated context's return keeps the binding pair**, on each of its four
arms: nothing to return, an unheld context popped back, a donated one returned,
or an unheld one severed. -/
theorem applyReplyDonationOnCore_bindingPair (st st' : SystemState) (rid : SeLe4n.ReplyId)
    (targetVtid : SeLe4n.ValidThreadId) (ownerHome : CoreId) (hObjInv : st.objects.invExt)
    (hP : schedContextBindingPair st)
    (h : applyReplyDonationOnCore st rid targetVtid ownerHome = .ok st') :
    schedContextBindingPair st' := by
  rcases applyReplyDonationOnCore_objects_frame st st' rid targetVtid ownerHome h with
    ⟨-, hEq⟩ | ⟨scId, n, s1, -, -, -, hRet, hA⟩ | ⟨scId, holder, n, s1, hRet, hA⟩ |
    ⟨scId, n, -, -, -, hSev⟩
  · exact hP.of_bindingLinksAgree (bindingLinksAgree.of_objects_eq hEq)
  · exact (returnUnheldSchedContext_bindingPair hObjInv hP hRet).of_bindingLinksAgree
      (bindingLinksAgree.of_offSchedulerLinks hA)
  · exact (returnDonatedSchedContext_bindingPair hObjInv hP hRet).of_bindingLinksAgree
      (bindingLinksAgree.of_offSchedulerLinks hA)
  · exact hP.of_schedLinkFrame (SchedLinkFrame.severUnheldSchedContext hObjInv hSev)

/-- **The cross-core reply dispatch keeps the binding pair**: the reply leg, the
donation return and the priority-inheritance revert. -/
theorem endpointReplyCrossCoreDispatch_bindingPair
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) (hP : schedContextBindingPair st) :
    schedContextBindingPair (endpointReplyCrossCoreDispatch replier target msg c st).1 := by
  have hRep := hP.of_bindingLinksAgree (endpointReplyOnCore_bindingLinksAgree replier target msg c st hObjInv)
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt replier target msg c st hObjInv
  unfold endpointReplyCrossCoreDispatch
  cases hRepEq : endpointReplyOnCore replier target msg c st with
  | mk st1 res1 =>
      rw [hRepEq] at hRep hInv1
      simp only at hRep hInv1 ⊢
      cases res1 with
      | error e => exact hP
      | ok replySgi? =>
          simp only
          split
          · split
            · split
              · exact hRep.of_schedLinkFrame (SchedLinkFrame.propagatePip _ _ _ _ hInv1)
              · split
                · exact hP
                · split
                  · exact hP
                  · rename_i st2 hRet
                    exact (applyReplyDonationOnCore_bindingPair _ _ _ _ _ hInv1 hRep hRet).of_schedLinkFrame
                      (SchedLinkFrame.propagatePip _ _ _ _
                        (applyReplyDonationOnCore_preserves_objects_invExt _ _ _ _ _ hInv1 hRet))
            · exact hP
          · split
            · exact hRep
            · split
              · exact hP
              · split
                · exact hP
                · rename_i st2 hRet
                  exact applyReplyDonationOnCore_bindingPair _ _ _ _ _ hInv1 hRep hRet

theorem endpointReplyCrossCoreDispatchChecked_bindingPair (ctx : LabelingContext)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) (hP : schedContextBindingPair st) :
    schedContextBindingPair (endpointReplyCrossCoreDispatchChecked ctx replier target msg c st).1 := by
  unfold endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch_bindingPair replier target msg c st hObjInv hP
  · exact hP

/-- The reply's capability transfer writes CNodes alone. -/
theorem replyTransferCaps_scIdLinksAgree (pre : SystemState) (replier caller : SeLe4n.ThreadId)
    (grant : Bool) {st st' : SystemState} {summary : CapTransferSummary}
    (hObjInv : st.objects.invExt)
    (h : replyTransferCaps pre replier caller grant st = .ok (summary, st')) :
    scIdLinksAgree st st' := by
  unfold replyTransferCaps at h
  obtain ⟨stR, caps, hO, -, -, hOr⟩ := receiveTransferCaps_frame h
  have hR : scIdLinksAgree st stR :=
    scIdLinksAgree.of_bindingLinksAgree (bindingLinksAgree.of_objects_eq hO)
  rcases hOr with rfl | ⟨rtcb, slot?, hU⟩
  · exact hR
  · have hInvR : stR.objects.invExt := hO ▸ hObjInv
    refine hR.trans ⟨fun x => ?_, fun s => by
      rw [ipcUnwrapCaps_getSchedContext?_eq caps none rtcb slot? stR st' summary s hInvR hU]⟩
    have e := congrArg (Option.map (fun t : TCB => t.schedContextBinding.scId?))
      (ipcUnwrapCaps_getTcb?_eq caps none rtcb slot? stR st' summary x hInvR hU)
    simpa only [Option.map_map, Function.comp_def] using e

/-- The delivered message's frame is a write of the answered thread's TCB. -/
theorem stageDeliveredMessage_scIdLinksAgree (st : SystemState) (tid : SeLe4n.ThreadId)
    (capInfo : Nat) (hObjInv : st.objects.invExt) :
    scIdLinksAgree st (Architecture.stageDeliveredMessage st tid capInfo) := by
  unfold Architecture.stageDeliveredMessage
  cases st.getTcb? tid with
  | none => exact .refl st
  | some tcb =>
    by_cases hReady : tcb.ipcState = .ready
    · simp only [hReady, if_pos]
      cases tcb.pendingMessage with
      | none => exact .refl st
      | some msg => exact scIdLinksAgree.updateTcb st tid _ hObjInv (fun _ => rfl)
    · simp only [hReady, if_false]; exact .refl st

/-- The fault reply's outcome: the restart frame installed, or the thread
abandoned (descheduled and `.Inactive`). -/
theorem faultReplyApplyOnCore_scIdLinksAgree (st : SystemState) (faulted : SeLe4n.ThreadId)
    (o : Architecture.FaultReplyOutcome) (hObjInv : st.objects.invExt) :
    scIdLinksAgree st (faultReplyApplyOnCore st faulted o) := by
  cases o with
  | restart frame => exact scIdLinksAgree.updateTcb st faulted _ hObjInv (fun _ => rfl)
  | abandon =>
    show scIdLinksAgree st (faultAbandonOnCore st faulted _)
    unfold faultAbandonOnCore
    exact (scIdLinksAgree.of_bindingLinksAgree (bindingLinksAgree.of_offRunLinks
      (removeRunnableOnCore_objectsAgreeOffRunLinks st faulted _))).trans
      (scIdLinksAgree.updateTcb _ faulted _
        (removeRunnableOnCore_objects_invExt st faulted _ hObjInv) (fun _ => rfl))

theorem faultReplyOnCore_bindingPair (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (c : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) (hP : schedContextBindingPair st) :
    schedContextBindingPair (faultReplyOnCore replier faulted mi regs c st).1 := by
  have hE := endpointReplyCrossCoreDispatch_bindingPair replier faulted IpcMessage.empty c st
    hObjInv hP
  have hI := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier faulted
    IpcMessage.empty c st hObjInv
  unfold faultReplyOnCore
  split
  · exact hP
  split
  · exact hP
  dsimp only
  split
  · exact hP
  · rename_i stR sgi hR
    rw [hR] at hE hI
    exact hE.of_scIdLinksAgree (faultReplyApplyOnCore_scIdLinksAgree _ _ _ hI)

/-- **The checked reply transfer keeps the binding pair**, on both of its
branches. -/
theorem replyTransferOnCoreChecked_bindingPair {ctx : LabelingContext}
    {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {grant : Bool} {c : CoreId}
    {st st' : SystemState} (hObjInv : st.objects.invExt) (hP : schedContextBindingPair st)
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant c st = .ok ((), st')) :
    schedContextBindingPair st' := by
  unfold replyTransferOnCoreChecked at h
  split at h
  · have hF := faultReplyOnCore_bindingPair replier callerTid mi regs c st hObjInv hP
    revert h hF
    generalize faultReplyOnCore replier callerTid mi regs c st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h _; cases h
    | ok _ => intro h hF; cases h; exact hF
  · have hE := endpointReplyCrossCoreDispatchChecked_bindingPair ctx replier callerTid msg c st
      hObjInv hP
    have hI : (endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg c st).1.objects.invExt := by
      unfold endpointReplyCrossCoreDispatchChecked
      split
      · exact endpointReplyCrossCoreDispatch_preserves_objects_invExt _ _ _ _ _ hObjInv
      · exact hObjInv
    revert h hE hI
    generalize endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg c st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h _ _; cases h
    | ok _ =>
      intro h hE hI
      simp only [] at h
      cases hX : replyTransferCaps st replier callerTid grant s with
      | error _ => rw [hX] at h; cases h
      | ok p =>
        obtain ⟨summary, sX⟩ := p
        rw [hX] at h
        cases h
        have hIX : sX.objects.invExt := by
          unfold replyTransferCaps at hX
          obtain ⟨stR, caps, hO, -, -, hOr⟩ := receiveTransferCaps_frame hX
          rcases hOr with rfl | ⟨rtcb, slot?, hU⟩
          · exact hO ▸ hI
          · exact ipcUnwrapCaps_preserves_objects_invExt caps none rtcb slot? stR sX summary
              (hO ▸ hI) hU
        exact (hE.of_scIdLinksAgree (replyTransferCaps_scIdLinksAgree st replier callerTid grant
          hI hX)).of_scIdLinksAgree (stageDeliveredMessage_scIdLinksAgree _ _ _ hIX)

/-! ### The home cores across a reply

seL4-MCS `handleReplyRecv`'s donation writes the receiver's home core: the core
its affinity names (`determineTargetCore`).  No leg of the reply writes a
thread's affinity — the return arms rewrite bindings and the migration moves a
context's reservation, never a thread — so the home core read on the entry
state is the one the donation writes (`replyTransferOnCoreChecked_homeCoresKept`). -/

/-- **Every thread keeps its home core.** -/
def homeCoresKept (st st' : SystemState) : Prop :=
  ∀ x : SeLe4n.ThreadId, determineTargetCore st' x = determineTargetCore st x

namespace homeCoresKept

theorem refl (st : SystemState) : homeCoresKept st st := fun _ => rfl

theorem trans {a b c : SystemState} (h₁ : homeCoresKept a b) (h₂ : homeCoresKept b c) :
    homeCoresKept a c := fun x => (h₂ x).trans (h₁ x)

theorem of_schedAuxAgree {st st' : SystemState} (h : schedAuxAgree st st') :
    homeCoresKept st st' := h.determineTargetCore_eq

theorem of_schedLinkFrame {st st' : SystemState} (h : SchedLinkFrame st st') :
    homeCoresKept st st' := of_schedAuxAgree h.aux

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    homeCoresKept st st' := of_schedAuxAgree (schedAuxAgree.of_objects_eq h)

theorem of_offRunLinks {st st' : SystemState} (h : st'.objectsAgreeOffRunLinks st) :
    homeCoresKept st st' := determineTargetCore_of_objectsAgreeOffRunLinks h

theorem of_offSchedulerLinks {st st' : SystemState} (h : st'.objectsAgreeOffSchedulerLinks st) :
    homeCoresKept st st' :=
  of_schedAuxAgree fun o => proj_eq_of_map_eq _ _ (fun x => by cases x <;> rfl) (h o)

/-- A step keeping every thread's placement keeps every home core. -/
theorem of_placement {st st' : SystemState}
    (h : ∀ x, (st'.getTcb? x).map TCB.placement = (st.getTcb? x).map TCB.placement) :
    homeCoresKept st st' := fun x =>
  determineTargetCore_congr st st' x (TCB.map_cpuAffinity_of_placement (h x))

/-- A thread rewritten in its slot keeping its budget and affinity. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).timeoutBudget = x.timeoutBudget ∧ (f x).cpuAffinity = x.cpuAffinity) :
    homeCoresKept st (st.updateTcb t f) :=
  of_schedAuxAgree (schedAuxAgree.updateTcb st t f hInv hf)

end homeCoresKept

/-- **The single-core reply keeps every home core**: the delivery store, a
link-only wake and the reply-frame removal. -/
theorem endpointReply_homeCoresKept
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    homeCoresKept st st' := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      split at hStep
      · cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
        | error e => simp [hMsg] at hStep
        | ok st'' =>
          simp only [hMsg] at hStep
          have h2 : homeCoresKept st (ensureRunnable st'' target) :=
            (homeCoresKept.of_schedLinkFrame
              (SchedLinkFrame.storeTcbIpcStateAndMessage hObjInv hMsg)).trans
              (homeCoresKept.of_offRunLinks (ensureRunnable_objectsAgreeOffRunLinks st'' target))
          have hObjInvMid : (ensureRunnable st'' target).objects.invExt := by
            apply ensureRunnable_objects_invExt
            exact storeTcbIpcStateAndMessage_preserves_objects_invExt st st'' target .ready
              (some msg) hObjInv hMsg
          cases hRO : tcb.replyObject with
          | none =>
            simp only [hRO, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
            rw [← hStep]
            exact h2.trans (homeCoresKept.of_offRunLinks
              (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ _ _))
          | some rid =>
            simp only [hRO] at hStep
            obtain ⟨st2, hRm, rfl⟩ := removeCallerReplyFrame_unlink_ok hStep
            exact (h2.trans (homeCoresKept.of_schedLinkFrame
              (SchedLinkFrame.removeCallerReplyFrame hObjInvMid hRm))).trans
              (homeCoresKept.of_offRunLinks
                (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ _ _))
      · simp at hStep

theorem endpointReplyOnCore_homeCoresKept
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    homeCoresKept st (endpointReplyOnCore replier target msg c st).1 := by
  rcases endpointReplyOnCore_post_agrees replier target msg c st hObjInv with
    hEq | ⟨expected, r1, hR, hA⟩
  · exact homeCoresKept.of_objects_eq (by rw [hEq])
  · exact (endpointReply_homeCoresKept st r1 expected target msg hObjInv hR).trans
      (homeCoresKept.of_offSchedulerLinks hA.objects)

/-- **The donated context's return keeps every home core**, on each of its four
arms: the returns rewrite bindings, never an affinity. -/
theorem applyReplyDonationOnCore_homeCoresKept (st st' : SystemState) (rid : SeLe4n.ReplyId)
    (targetVtid : SeLe4n.ValidThreadId) (ownerHome : CoreId) (hObjInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st rid targetVtid ownerHome = .ok st') :
    homeCoresKept st st' := by
  rcases applyReplyDonationOnCore_objects_frame st st' rid targetVtid ownerHome h with
    ⟨-, hEq⟩ | ⟨scId, n, s1, -, -, -, hRet, hA⟩ | ⟨scId, holder, n, s1, hRet, hA⟩ |
    ⟨scId, n, -, -, -, hSev⟩
  · exact homeCoresKept.of_objects_eq hEq
  · exact (homeCoresKept.of_placement fun x =>
      returnUnheldSchedContext_getTcb?_placement_eq hObjInv hRet x).trans
      (homeCoresKept.of_offSchedulerLinks hA)
  · exact (homeCoresKept.of_placement fun x =>
      returnDonatedSchedContext_getTcb?_placement_eq _ _ _ _ _ hObjInv _ hRet x).trans
      (homeCoresKept.of_offSchedulerLinks hA)
  · exact homeCoresKept.of_schedLinkFrame (SchedLinkFrame.severUnheldSchedContext hObjInv hSev)

/-- **The cross-core reply dispatch keeps every home core**: the reply leg, the
donation return and the priority-inheritance revert. -/
theorem endpointReplyCrossCoreDispatch_homeCoresKept
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    homeCoresKept st (endpointReplyCrossCoreDispatch replier target msg c st).1 := by
  have hRep := endpointReplyOnCore_homeCoresKept replier target msg c st hObjInv
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt replier target msg c st hObjInv
  unfold endpointReplyCrossCoreDispatch
  cases hRepEq : endpointReplyOnCore replier target msg c st with
  | mk st1 res1 =>
      rw [hRepEq] at hRep hInv1
      simp only at hRep hInv1 ⊢
      cases res1 with
      | error e => exact .refl st
      | ok replySgi? =>
          simp only
          split
          · split
            · split
              · exact hRep.trans (homeCoresKept.of_schedLinkFrame
                  (SchedLinkFrame.propagatePip _ _ _ _ hInv1))
              · split
                · exact .refl st
                · split
                  · exact .refl st
                  · rename_i st2 hRet
                    exact (hRep.trans (applyReplyDonationOnCore_homeCoresKept _ _ _ _ _ hInv1
                      hRet)).trans (homeCoresKept.of_schedLinkFrame (SchedLinkFrame.propagatePip _ _ _ _
                        (applyReplyDonationOnCore_preserves_objects_invExt _ _ _ _ _ hInv1 hRet)))
            · exact .refl st
          · split
            · exact hRep
            · split
              · exact .refl st
              · split
                · exact .refl st
                · rename_i st2 hRet
                  exact hRep.trans (applyReplyDonationOnCore_homeCoresKept _ _ _ _ _ hInv1 hRet)

theorem endpointReplyCrossCoreDispatchChecked_homeCoresKept (ctx : LabelingContext)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    homeCoresKept st (endpointReplyCrossCoreDispatchChecked ctx replier target msg c st).1 := by
  unfold endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch_homeCoresKept replier target msg c st hObjInv
  · exact .refl st

/-- The reply's capability transfer writes CNodes alone. -/
theorem replyTransferCaps_homeCoresKept (pre : SystemState) (replier caller : SeLe4n.ThreadId)
    (grant : Bool) {st st' : SystemState} {summary : CapTransferSummary}
    (hObjInv : st.objects.invExt)
    (h : replyTransferCaps pre replier caller grant st = .ok (summary, st')) :
    homeCoresKept st st' := fun x => by
  unfold replyTransferCaps at h
  exact receiveTransferCaps_determineTargetCore_eq x hObjInv h

/-- The delivered message's frame is a write of the answered thread's registers. -/
theorem stageDeliveredMessage_homeCoresKept (st : SystemState) (tid : SeLe4n.ThreadId)
    (capInfo : Nat) (hObjInv : st.objects.invExt) :
    homeCoresKept st (Architecture.stageDeliveredMessage st tid capInfo) := by
  unfold Architecture.stageDeliveredMessage
  cases st.getTcb? tid with
  | none => exact .refl st
  | some tcb =>
    by_cases hReady : tcb.ipcState = .ready
    · simp only [hReady, if_pos]
      cases tcb.pendingMessage with
      | none => exact .refl st
      | some msg => exact homeCoresKept.updateTcb st tid _ hObjInv (fun _ => ⟨rfl, rfl⟩)
    · simp only [hReady, if_false]; exact .refl st

theorem faultReplyApplyOnCore_homeCoresKept (st : SystemState) (faulted : SeLe4n.ThreadId)
    (o : Architecture.FaultReplyOutcome) (hObjInv : st.objects.invExt) :
    homeCoresKept st (faultReplyApplyOnCore st faulted o) := by
  cases o with
  | restart frame => exact homeCoresKept.updateTcb st faulted _ hObjInv (fun _ => ⟨rfl, rfl⟩)
  | abandon =>
    show homeCoresKept st (faultAbandonOnCore st faulted _)
    unfold faultAbandonOnCore
    exact (homeCoresKept.of_offRunLinks
      (removeRunnableOnCore_objectsAgreeOffRunLinks st faulted _)).trans
      (homeCoresKept.updateTcb _ faulted _
        (removeRunnableOnCore_objects_invExt st faulted _ hObjInv) (fun _ => ⟨rfl, rfl⟩))

theorem faultReplyOnCore_homeCoresKept (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (c : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    homeCoresKept st (faultReplyOnCore replier faulted mi regs c st).1 := by
  have hE := endpointReplyCrossCoreDispatch_homeCoresKept replier faulted IpcMessage.empty c st
    hObjInv
  have hI := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier faulted
    IpcMessage.empty c st hObjInv
  unfold faultReplyOnCore
  split
  · exact .refl st
  split
  · exact .refl st
  dsimp only
  split
  · exact .refl st
  · rename_i stR sgi hR
    rw [hR] at hE hI
    exact hE.trans (faultReplyApplyOnCore_homeCoresKept _ _ _ hI)

/-- **The checked reply transfer keeps every home core**, on both of its
branches. -/
theorem replyTransferOnCoreChecked_homeCoresKept {ctx : LabelingContext}
    {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {grant : Bool} {c : CoreId}
    {st st' : SystemState} (hObjInv : st.objects.invExt)
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant c st = .ok ((), st')) :
    homeCoresKept st st' := by
  unfold replyTransferOnCoreChecked at h
  split at h
  · have hF := faultReplyOnCore_homeCoresKept replier callerTid mi regs c st hObjInv
    revert h hF
    generalize faultReplyOnCore replier callerTid mi regs c st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h _; cases h
    | ok _ => intro h hF; cases h; exact hF
  · have hE := endpointReplyCrossCoreDispatchChecked_homeCoresKept ctx replier callerTid msg c st
      hObjInv
    have hI : (endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg c st).1.objects.invExt := by
      unfold endpointReplyCrossCoreDispatchChecked
      split
      · exact endpointReplyCrossCoreDispatch_preserves_objects_invExt _ _ _ _ _ hObjInv
      · exact hObjInv
    revert h hE hI
    generalize endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg c st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h _ _; cases h
    | ok _ =>
      intro h hE hI
      simp only [] at h
      cases hX : replyTransferCaps st replier callerTid grant s with
      | error _ => rw [hX] at h; cases h
      | ok p =>
        obtain ⟨summary, sX⟩ := p
        rw [hX] at h
        cases h
        have hIX : sX.objects.invExt := by
          unfold replyTransferCaps at hX
          obtain ⟨stR, caps, hO, -, -, hOr⟩ := receiveTransferCaps_frame hX
          rcases hOr with rfl | ⟨rtcb, slot?, hU⟩
          · exact hO ▸ hI
          · exact ipcUnwrapCaps_preserves_objects_invExt caps none rtcb slot? stR sX summary
              (hO ▸ hI) hU
        exact (hE.trans (replyTransferCaps_homeCoresKept st replier callerTid grant hI hX)).trans
          (stageDeliveredMessage_homeCoresKept _ _ _ hIX)

/-! ### The notifications' context words across a reply -/

/-- **A step that keeps, and creates, no notification keeps every context
word.** -/
theorem ntfnContextsAgree.of_notificationsAndBindingsKept {st st' : SystemState}
    (h : notificationsAndBindingsKept st st') : ntfnContextsAgree st st' := by
  intro oid
  by_cases hN : ∃ n, st'.objects[oid]? = some (.notification n)
  · obtain ⟨n, hn⟩ := hN
    rw [hn, h.2.2 oid n hn]
  · have hN' : ¬ ∃ m, st.objects[oid]? = some (.notification m) :=
      fun ⟨m, hm⟩ => hN ⟨m, h.1 oid m hm⟩
    have e : ∀ (o : Option KernelObject), (¬ ∃ m, o = some (.notification m)) →
        ntfnContextOf o = none := by
      intro o ho
      cases o with
      | none => rfl
      | some o => cases o <;> first | rfl | exact absurd ⟨_, rfl⟩ ho
    rw [e _ hN, e _ hN']

/-- States agreeing on every context word name the same context for every
notification. -/
theorem notificationContext?_congr {st st' : SystemState} (h : ntfnContextsAgree st st')
    (n : SeLe4n.ObjId) : notificationContext? st' n = notificationContext? st n := by
  have e := h.getNotification?_schedContext n
  unfold notificationContext?
  cases h1 : st'.getNotification? n <;> cases h2 : st.getNotification? n <;>
    rw [h1, h2] at e <;> simp_all

/-- **The checked reply transfer keeps the object store's extension invariant**,
on both of its branches. -/
theorem replyTransferOnCoreChecked_objects_invExt {ctx : LabelingContext}
    {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {grant : Bool} {c : CoreId}
    {st st' : SystemState} (hObjInv : st.objects.invExt)
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant c st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold replyTransferOnCoreChecked at h
  split at h
  · have hF := faultReplyOnCore_preserves_objects_invExt replier callerTid mi regs c st hObjInv
    revert h hF
    generalize faultReplyOnCore replier callerTid mi regs c st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h _; cases h
    | ok _ => intro h hF; cases h; exact hF
  · have hI : (endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg c st).1.objects.invExt := by
      unfold endpointReplyCrossCoreDispatchChecked
      split
      · exact endpointReplyCrossCoreDispatch_preserves_objects_invExt _ _ _ _ _ hObjInv
      · exact hObjInv
    revert h hI
    generalize endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg c st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h _; cases h
    | ok _ =>
      intro h hI
      simp only [] at h
      cases hX : replyTransferCaps st replier callerTid grant s with
      | error _ => rw [hX] at h; cases h
      | ok p =>
        obtain ⟨summary, sX⟩ := p
        rw [hX] at h
        cases h
        have hIX : sX.objects.invExt := by
          unfold replyTransferCaps at hX
          obtain ⟨stR, caps, hO, -, -, hOr⟩ := receiveTransferCaps_frame hX
          rcases hOr with rfl | ⟨rtcb, slot?, hU⟩
          · exact hO ▸ hI
          · exact ipcUnwrapCaps_preserves_objects_invExt caps none rtcb slot? stR sX summary
              (hO ▸ hI) hU
        exact stageDeliveredMessage_objects_invExt _ _ _ hIX

end SeLe4n.Kernel
