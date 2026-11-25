/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SavedRegistersSendNotification

/-!
# The saved-register census over the call, receive and reply arms

WS-ZA ZA6.26.  The `.call`, `.receive`, `.reply` and `.replyRecv` arms of
`dispatchWithCapChecked`, each read as the threads it writes
(`savedRegsWrittenFree`, at the entry's start).

* **The transitions write no saved register** (`savedRegsUnwritten`).  The
  call blocks its caller and hands its receiver the message as a pending
  message; the reply links, the scheduling-context lend and its return, the
  priority-inheritance walks and the deschedules write reply objects, binding
  words, boosts and run-queue links; the reply's delivery and the receive's
  completion are pending messages and IPC states.
* **The woken receiver's delivery names the receive queue's head** at the
  entry's start, blocked there (`offCoreFree_of_receiveHead`); **the send's
  completion names the send queue's head** (`offCoreFree_of_sendHead`).
* **The reply's staging names the answered caller**, whom the reply leg refuses
  unless it is blocked on its reply (`endpointReplyCrossCoreDispatch_ok_target_notReady`);
  the fault reply's restart frame likewise.  The receive's delivered message is
  staged into the caller, the executing core's current thread.

A thread blocked at the entry's start is current nowhere and, by
`blockedNotResident`, resident nowhere (`offCoreFree_of_notReady`).
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-! ### The reply links and the lend -/

namespace savedRegsUnwritten

theorem of_kept {st st' : SystemState} (h : savedRegsKeptExcept (fun _ => False) st st')
    (hInv : st'.objects.invExt) : savedRegsUnwritten st st' := ⟨h, hInv⟩

theorem of_linkReply {rid : SeLe4n.ReplyId} {caller : SeLe4n.ThreadId} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : SystemState.linkReply rid caller st = .ok ((), st')) :
    savedRegsUnwritten st st' := by
  unfold SystemState.linkReply at h
  cases hR : st.getReply? rid with
  | none => simp [hR] at h
  | some r =>
    simp only [hR] at h
    split at h
    · exact of_storeObject_after (fun x hx => by
        rw [(SystemState.getReply?_eq_some_iff st rid r).mp hR] at hx; cases hx)
        (fun x hx => by cases hx) (.refl hInv) h
    · simp at h

theorem of_linkCallerReply {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    savedRegsUnwritten st st' := by
  unfold SystemState.linkCallerReply at h
  cases hLink : SystemState.linkReply rid caller st with
  | error e => simp [hLink] at h
  | ok p1 =>
    obtain ⟨⟨⟩, st1⟩ := p1
    simp only [hLink] at h
    have hF1 := of_linkReply hInv hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at h
    | some tcb =>
      simp only [hT] at h
      split at h
      · refine hF1.trans (of_storeObject_tcb_after
          ((SystemState.getTcb?_eq_some_iff st1 caller tcb).mp hT) ?_ (.refl hF1.2) h)
        rfl
      · simp at h

theorem of_linkServerStashedReply {caller server : SeLe4n.ThreadId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    savedRegsUnwritten st st' := by
  unfold SystemState.linkServerStashedReply at h
  split at h
  · cases h
  · rename_i rid _
    cases hL : SystemState.linkCallerReply caller rid st with
    | error _ => simp [hL] at h
    | ok p1 =>
      obtain ⟨⟨⟩, st1⟩ := p1
      simp only [hL] at h
      have hF1 := of_linkCallerReply hInv hL
      split at h
      · cases h; exact hF1
      · rename_i sTcb hT
        refine hF1.trans (of_storeObject_tcb_after
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) ?_ (.refl hF1.2) h)
        rfl

theorem of_linkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    savedRegsUnwritten st (st.linkReplyWaiter w s) :=
  ⟨.of_replyLinks (SystemState.linkReplyWaiter_objectsAgreeOffReplyLinks _ _ _),
    SystemState.linkReplyWaiter_objects_invExt _ _ _ hInv⟩

theorem of_unlinkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : savedRegsUnwritten st (st.unlinkReplyWaiter w s) :=
  ⟨.of_replyLinks (SystemState.unlinkReplyWaiter_objectsAgreeOffReplyLinks _ _ _),
    SystemState.unlinkReplyWaiter_objects_invExt _ _ _ hInv⟩

/-- WS-ZA ZA6.34: the unlink of a caller whose recorded server may be none. -/
theorem of_unlinkReplyWaiterOpt (st : SystemState) (w : SeLe4n.ThreadId)
    (s? : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    savedRegsUnwritten st (st.unlinkReplyWaiterOpt w s?) :=
  ⟨.of_replyLinks (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks _ _ _),
    SystemState.unlinkReplyWaiterOpt_objects_invExt _ _ _ hInv⟩

theorem of_migrate (st : SystemState) (scId : SeLe4n.SchedContextId) (a b : CoreId)
    (hInv : st.objects.invExt) :
    savedRegsUnwritten st (migrateSchedContextReplenishment st scId a b) :=
  ⟨.of_releaseLinks (migrateSchedContextReplenishment_agree _ _ _ _),
    migrateSchedContextReplenishment_preserves_objects_invExt _ _ _ _ hInv⟩

/-- WS-ZA ZA6.33: the settle of a returned context writes release links alone. -/
theorem of_settle (st : SystemState) (c : CoreId) (scId : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) :
    savedRegsUnwritten st (SchedContextOps.settleReturnedContext st c scId) :=
  ⟨.of_releaseLinks (SchedContextOps.settleReturnedContext_agree _ _ _),
    SchedContextOps.settleReturnedContext_objects_invExt _ _ _ hInv⟩

theorem of_descheduleAt (st : SystemState) (tid : SeLe4n.ThreadId) (placed : Option CoreId)
    (hInv : st.objects.invExt) : savedRegsUnwritten st (descheduleAt st tid placed) := by
  unfold descheduleAt
  cases placed with
  | none => exact .refl hInv
  | some c => exact of_removeRunnableOnCore st tid c hInv

theorem of_propagate (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) (fuel : Nat)
    (hInv : st.objects.invExt) :
    savedRegsUnwritten st (PriorityInheritance.propagatePipChainCrossCore st tid c fuel).1 :=
  ⟨.of_propagatePipChainCrossCore st tid c fuel hInv,
    (propagatePipChainCrossCore_stepCovers c c fuel st tid hInv).2⟩

end savedRegsUnwritten

namespace savedRegsUnwritten

/-- The lend rebinds the donor's and the server's scheduling contexts. -/
theorem of_donateSchedContext {st st' : SystemState} {clientTid serverTid : SeLe4n.ThreadId}
    {clientScId : SeLe4n.SchedContextId} (hInv : st.objects.invExt)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    savedRegsUnwritten st st' :=
  ⟨.of_map (donateSchedContext_getTcb?_map_eq TCB.registerContext (fun _ _ _ => rfl) st st'
      clientTid serverTid clientScId hInv h),
    donateSchedContext_preserves_objects_invExt _ _ _ _ _ hInv h⟩

theorem of_applyCallDonation {st st' : SystemState} {callerVtid receiverVtid : SeLe4n.ValidThreadId}
    (hInv : st.objects.invExt) (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    savedRegsUnwritten st st' := by
  unfold applyCallDonation at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact .refl hInv)
    | (cases h; rename_i hD; exact of_donateSchedContext hInv hD)
    | (cases h; done)

theorem of_applyCallDonationOnCore {st st' : SystemState}
    {callerVtid receiverVtid : SeLe4n.ValidThreadId} {donorHome doneeHome : CoreId}
    (hInv : st.objects.invExt)
    (h : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st') :
    savedRegsUnwritten st st' := by
  obtain ⟨st1, hDon, hArm⟩ := applyCallDonationOnCore_ok_decompose _ _ _ _ _ _ h
  have h1 := of_applyCallDonation hInv hDon
  rcases hArm with ⟨_, rfl⟩ | ⟨scId, _, rfl⟩
  · exact h1
  · exact h1.trans (of_migrate _ _ _ _ h1.2)

theorem of_applyRendezvousCallDonation {st st' : SystemState} {receiver donor : SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : applyRendezvousCallDonation st receiver donor = .ok st') :
    savedRegsUnwritten st st' := by
  unfold applyRendezvousCallDonation at h
  split at h
  · exact of_applyCallDonationOnCore hInv h
  · cases h

end savedRegsUnwritten

/-! ### Call -/

/-- The per-core call writes no saved register: the rendezvous hands the
receiver the message as a pending message, wakes it, blocks the caller on its
reply, links the reply objects, deschedules the caller and queues it on the
server's reply waiters; a call that links no reply hands the message over,
wakes the receiver, deschedules the caller and writes it `Inactive`; the block appends the caller, stores its state,
deschedules it and records its capability's bits. -/
theorem endpointCallOnCore_savedRegsUnwritten (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload) (c : CoreId) {st : SystemState}
    (hInv : st.objects.invExt) :
    savedRegsUnwritten st (endpointCallOnCore endpointId caller payload c st).1 := by
  unfold endpointCallOnCore
  split
  · split
    · split
      · split
        · exact .refl hInv
        · rename_i receiver _tcb st1 hPop
          have h1 := endpointQueuePopHead_savedRegsUnwritten hInv hPop
          split
          · exact .refl hInv
          · rename_i st2 hRdy
            have h2 := h1.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage h1.2 hRdy)
            have hW := h2.trans (savedRegsUnwritten.of_wakeThread st2 receiver c h2.2)
            split
            · exact .refl hInv
            · rename_i st4 hBlk
              have h4 := hW.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage hW.2 hBlk)
              split
              · exact .refl hInv
              · rename_i st5 hLink
                have h5 := h4.trans (savedRegsUnwritten.of_linkServerStashedReply h4.2 hLink)
                have h6 := h5.trans (savedRegsUnwritten.of_removeRunnableOnCore st5 caller c h5.2)
                exact h6.trans (savedRegsUnwritten.of_linkReplyWaiter _ _ _ h6.2)
      · -- A call that links no reply: the receiver's delivery and wake, the
        -- caller's deschedule, and its `Inactive` write, none a saved register.
        split
        · exact .refl hInv
        · rename_i receiver _tcb st1 hPop
          have h1 := endpointQueuePopHead_savedRegsUnwritten hInv hPop
          split
          · exact .refl hInv
          · rename_i st2 hRC
            split
            · exact .refl hInv
            have h2 := h1.trans (savedRegsUnwritten.of_storeTcbReceiveComplete h1.2 hRC)
            have hW := h2.trans (savedRegsUnwritten.of_wakeThread st2 receiver c h2.2)
            have h3 := hW.trans (savedRegsUnwritten.of_removeRunnableOnCore _ caller c hW.2)
            exact ⟨h3.kept.trans (.updateTcb _ _ _ h3.2 fun _ => rfl),
              SystemState.updateTcb_preserves_objects_invExt _ _ _ h3.2⟩
    · split
      · exact .refl hInv
      · rename_i st1 hEnq
        have h1 := endpointQueueEnqueue_savedRegsUnwritten hInv hEnq
        split
        · exact .refl hInv
        · rename_i st2 hBlk
          have h2 := h1.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage h1.2 hBlk)
          have h3 := h2.trans (savedRegsUnwritten.of_removeRunnableOnCore st2 caller c h2.2)
          exact h3.trans (savedRegsUnwritten.of_recordSendCap _ caller _ _ _ h3.2)
  · split <;> exact .refl hInv

theorem endpointCallWithCapsOnCore_savedRegsUnwritten (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload) (c : CoreId)
    {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st (endpointCallWithCapsOnCore endpointId caller payload c st).1 := by
  have h0 := endpointCallOnCore_savedRegsUnwritten endpointId caller payload c hInv
  unfold endpointCallWithCapsOnCore
  generalize endpointCallOnCore endpointId caller payload c st = r at h0
  obtain ⟨st1, r⟩ := r
  cases r with
  | error _ => exact h0
  | ok _ =>
    dsimp only
    repeat' split
    all_goals first
      | exact h0
      | (rename_i hU; exact h0.trans (receiveTransferCaps_savedRegsUnwritten h0.2 hU))

/-- The live call writes no saved register: the rendezvous, the lend to a
passive receiver, and the chain walk from it. -/
theorem endpointCallCrossCoreDispatch_savedRegsUnwritten (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload) (c : CoreId)
    {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st (endpointCallCrossCoreDispatch endpointId caller payload c st).1 := by
  have h0 := endpointCallWithCapsOnCore_savedRegsUnwritten endpointId caller payload c hInv
  unfold endpointCallCrossCoreDispatch
  generalize endpointCallWithCapsOnCore endpointId caller payload c st = r at h0
  obtain ⟨st1, r⟩ := r
  cases r with
  | error _ => exact h0
  | ok p =>
    obtain ⟨summary, sgi⟩ := p
    dsimp only
    repeat' split
    all_goals first
      | exact h0
      | (rename_i hD
         have h1 := h0.trans (savedRegsUnwritten.of_applyCallDonationOnCore h0.2 hD)
         exact h1.trans (savedRegsUnwritten.of_propagate _ _ _ _ h1.2))

theorem endpointCallCrossCoreDispatchChecked_savedRegsUnwritten (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (c : CoreId) {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st
      (endpointCallCrossCoreDispatchChecked ctx endpointId caller payload c st).1 := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · exact endpointCallCrossCoreDispatch_savedRegsUnwritten _ _ _ _ hInv
  · exact .refl hInv

/-! ### The donation returns and the reply objects -/

namespace savedRegsUnwritten

theorem of_returnDonatedSchedContextResolved {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : returnDonatedSchedContextResolved st serverTid scId owner = .ok st') :
    savedRegsUnwritten st st' := by
  obtain ⟨newOwner?, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose h
  exact ⟨.of_map fun x => returnDonatedSchedContext_getTcb?_map_eq TCB.registerContext
      (fun _ _ _ => rfl) _ st' serverTid scId owner hInv newOwner? hPop x,
    (returnDonatedSchedContextResolved_stepCovers Concurrency.bootCoreId hInv h).2⟩

/-- The unheld pop rewrites the recipient's binding codes and no thread's
registers. -/
theorem of_returnUnheldSchedContext {st st' : SystemState} {scId : SeLe4n.SchedContextId}
    {owner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    savedRegsUnwritten st st' := by
  refine ⟨.of_map fun x => ?_, returnUnheldSchedContext_objects_invExt hInv h⟩
  obtain ⟨_, _, ot, -, -, -, -, hO, -, -, hO', tBwd, tFwd, -, -⟩ :=
    returnUnheldSchedContext_objects hInv h
  by_cases e : x.toObjId = owner.toObjId
  · rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr (e ▸ hO'),
      (SystemState.getTcb?_eq_some_iff _ _ _).mpr (e ▸ hO)]
    rfl
  · cases h1 : st.getTcb? x with
    | some t0 =>
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr
        (tFwd _ _ e ((SystemState.getTcb?_eq_some_iff _ _ _).mp h1))]
    | none =>
      cases h2 : st'.getTcb? x with
      | none => rfl
      | some t1 =>
        have := tBwd _ _ e ((SystemState.getTcb?_eq_some_iff _ _ _).mp h2)
        rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr this] at h1
        cases h1

/-- The held pop rewrites one thread's binding codes, no saved register. -/
theorem of_keepDonatedSchedContext {st st' : SystemState} {holder : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {newOwner? : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : keepDonatedSchedContext st holder scId newOwner? = .ok st') :
    savedRegsUnwritten st st' := by
  refine ⟨.of_map fun x => ?_, keepDonatedSchedContext_objects_invExt hInv h⟩
  obtain ⟨_, _, ot, -, -, -, -, hO, -, -, hO', tBwd, tFwd, -, -⟩ :=
    keepDonatedSchedContext_objects hInv h
  by_cases e : x.toObjId = holder.toObjId
  · rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr (e ▸ hO'),
      (SystemState.getTcb?_eq_some_iff _ _ _).mpr (e ▸ hO)]
    rfl
  · cases h1 : st.getTcb? x with
    | some t0 =>
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr
        (tFwd _ _ e ((SystemState.getTcb?_eq_some_iff _ _ _).mp h1))]
    | none =>
      cases h2 : st'.getTcb? x with
      | none => rfl
      | some t1 =>
        have := tBwd _ _ e ((SystemState.getTcb?_eq_some_iff _ _ _).mp h2)
        rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr this] at h1
        cases h1

/-- The resolved held pop. -/
theorem of_keepDonatedSchedContextResolved {st st' : SystemState} {holder : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} (hInv : st.objects.invExt)
    (h : keepDonatedSchedContextResolved st holder scId = .ok st') : savedRegsUnwritten st st' :=
  keepDonatedSchedContextResolved_lift h fun _ _ hP => of_keepDonatedSchedContext hInv hP

/-- The pop at an unheld head: the unheld pop, then the settle; or the sever,
which writes no thread. -/
theorem of_popUnheldReplyHead {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} {home : CoreId} (hInv : st.objects.invExt)
    (h : popUnheldReplyHead st rid target home = .ok st') : savedRegsUnwritten st st' := by
  rcases popUnheldReplyHead_objects_frame h with ⟨-, rfl⟩ | ⟨scId, _, st1, -, -, hP, rfl⟩ |
      ⟨_, _, -, -, hS⟩
  · exact .refl hInv
  rotate_left
  · exact ⟨.of_map fun x => by rw [severUnheldSchedContext_getTcb?_eq hInv hS],
      severUnheldSchedContext_objects_invExt hInv hS⟩
  · have h1 := of_returnUnheldSchedContext hInv hP
    exact h1.trans (of_settle _ _ _ h1.2)

/-- The pre-receive cleanup pops the held head (returning the context or keeping
it with the receiver) and migrates its replenishments. -/
theorem of_cleanupPreReceiveDonationMigrated {st st' : SystemState} {receiver : SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : cleanupPreReceiveDonationMigrated st receiver = .ok st') :
    savedRegsUnwritten st st' := by
  obtain ⟨stClean, hC, rfl⟩ := cleanupPreReceiveDonationMigrated_ok_decompose h
  have hClean : savedRegsUnwritten st stClean := by
    unfold cleanupPreReceiveDonationChecked at hC
    split at hC
    · cases hC; exact .refl hInv
    · split at hC
      · exact popHeldReplyHead_lift hC (fun _ _ hR => of_returnDonatedSchedContextResolved hInv hR)
          (fun _ _ hK => of_keepDonatedSchedContextResolved hInv hK)
      · cases hC; exact .refl hInv
  refine hClean.trans ?_
  unfold preReceiveReturnMigration
  split
  · exact of_migrate _ _ _ _ hClean.2
  · exact .refl hClean.2

theorem of_consumeCallerReply {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    savedRegsUnwritten st st' := by
  unfold SystemState.consumeCallerReply at h
  cases hC : SystemState.consumeReply rid st with
  | error _ => simp [hC] at h
  | ok p1 =>
    obtain ⟨⟨⟩, st1⟩ := p1
    simp only [hC] at h
    have hF1 : savedRegsUnwritten st st1 := by
      unfold SystemState.consumeReply at hC
      split at hC
      · rename_i r hR
        exact of_storeObject_after (fun x hx => by
          rw [(SystemState.getReply?_eq_some_iff st rid r).mp hR] at hx; cases hx)
          (fun x hx => by cases hx) (.refl hInv) hC
      · cases hC; exact .refl hInv
    split at h
    · cases h; exact hF1
    · rename_i tcb hT
      refine hF1.trans (of_storeObject_tcb_after
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) ?_ (.refl hF1.2) h)
      rfl

theorem of_cutReplyFrameOutOrSelf (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) : savedRegsUnwritten st (cutReplyFrameOutOrSelf st rid) := by
  refine ⟨?_, cutReplyFrameOutOrSelf_preserves_objects_invExt st rid hInv⟩
  rcases cutReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]; exact .refl _
  · exact .of_map fun x => by rw [cutReplyFrameOut_getTcb?_eq hInv h x]

theorem of_removeCallerReplyFrame {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : removeCallerReplyFrame caller rid st = .ok ((), st')) : savedRegsUnwritten st st' := by
  unfold removeCallerReplyFrame at h
  have h1 := of_cutReplyFrameOutOrSelf st rid hInv
  exact h1.trans (of_consumeCallerReply h1.2 h)

theorem of_storeTcbIpcStateAndMessage_fromTcb {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} {ipc : ThreadIpcState} {msg : Option IpcMessage} (hInv : st.objects.invExt)
    (hL : lookupTcb st tid = some tcb)
    (h : storeTcbIpcStateAndMessage_fromTcb st tid tcb ipc msg = .ok st') :
    savedRegsUnwritten st st' := by
  unfold storeTcbIpcStateAndMessage_fromTcb at h
  revert h
  cases hSt : storeObject tid.toObjId _ st with
  | error _ => intro h; cases h
  | ok p =>
    obtain ⟨⟨⟩, s⟩ := p
    intro h; cases h
    refine of_storeObject_tcb_after (lookupTcb_some_objects _ _ _ hL) ?_ (.refl hInv) hSt
    rfl

theorem of_recordReplyStasher (st : SystemState) (code : Nat) (recv : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : savedRegsUnwritten st (st.recordReplyStasher code recv) :=
  ⟨.of_map fun x => by rw [SystemState.recordReplyStasher_getTcb? st code recv hInv x],
    SystemState.recordReplyStasher_objects_invExt st code recv hInv⟩

end savedRegsUnwritten

/-! ### Receive -/

/-- The per-core receive writes no saved register: a call rendezvous blocks the
caller on its reply, links the reply objects, hands the receiver the message as
a pending message and queues the caller on its reply waiters; a send rendezvous
readies and wakes the sender and hands the receiver the message; the block runs
the pre-receive cleanup, appends the receiver, stores its state, records the
stashed reply and deschedules it. -/
theorem endpointReceiveDualOnCore_savedRegsUnwritten (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (c : CoreId)
    {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st (endpointReceiveDualOnCore endpointId receiver replyId c st).1 := by
  unfold endpointReceiveDualOnCore
  split
  · split
    · split
      · exact .refl hInv
      · rename_i sender senderTcb st1 hPop
        have h1 := endpointQueuePopHead_savedRegsUnwritten hInv hPop
        dsimp only
        split <;> simp only [↓reduceIte, Bool.false_eq_true]
        · split
          · split
            · exact .refl hInv
            · rename_i st2 hBlk
              have h2 := h1.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage h1.2 hBlk)
              split
              · exact .refl hInv
              · split
                · exact .refl hInv
                · rename_i stL hL
                  have h3 := h2.trans (savedRegsUnwritten.of_linkCallerReply h2.2 hL)
                  split
                  · rename_i st4 hRdy
                    have h4 := h3.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage h3.2 hRdy)
                    exact h4.trans (savedRegsUnwritten.of_linkReplyWaiter _ _ _ h4.2)
                  · exact .refl hInv
          · -- a `Call` that links no reply: the caller's `Inactive` mark writes no register
            split
            · exact .refl hInv
            · rename_i st2 hRdy
              have h2 := h1.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage h1.2 hRdy)
              have h3 := h2.trans (savedRegsUnwritten.of_updateTcb st2 sender
                (fun t => { t with threadState := .Inactive }) h2.2 (fun _ => rfl))
              split
              · rename_i st4 hRcv
                exact h3.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage h3.2 hRcv)
              · exact .refl hInv
        · split
          · exact .refl hInv
          · rename_i st2 hRdy
            have h2 := h1.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage h1.2 hRdy)
            have hW := h2.trans (savedRegsUnwritten.of_wakeThread st2 sender c h2.2)
            split
            · rename_i st4 hRcv
              exact hW.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage hW.2 hRcv)
            · exact .refl hInv
    · split
      · exact .refl hInv
      · rename_i stClean hClean
        have hC := savedRegsUnwritten.of_cleanupPreReceiveDonationMigrated hInv hClean
        split
        · exact .refl hInv
        · rename_i st1 hEnq
          have h1 := hC.trans (endpointQueueEnqueue_savedRegsUnwritten hC.2 hEnq)
          split
          · exact .refl hInv
          · rename_i st2 hBlk
            have h2 := h1.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage h1.2 hBlk)
            split
            · exact h2.trans (savedRegsUnwritten.of_removeRunnableOnCore _ _ _ h2.2)
            · rename_i rTcb hT
              split
              · split
                · exact .refl hInv
                · rename_i stS hS
                  have hR := h2.trans (savedRegsUnwritten.of_recordReplyStasher _
                    (SeLe4n.ReplyId.optCode replyId) receiver h2.2)
                  have h3 : savedRegsUnwritten st stS := by
                    refine hR.trans (savedRegsUnwritten.of_storeObject_tcb_after (t := rTcb)
                      ((SystemState.getTcb?_eq_some_iff _ _ _).mp (by
                        rw [SystemState.recordReplyStasher_getTcb? _ _ _ h2.2]; exact hT)) ?_
                      (.refl hR.2) hS)
                    rfl
                  exact h3.trans (savedRegsUnwritten.of_removeRunnableOnCore _ _ _ h3.2)
              · exact .refl hInv
  · split <;> exact .refl hInv

theorem endpointReceiveDualWithCapsOnCore_savedRegsUnwritten (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (c : CoreId) {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st
      (endpointReceiveDualWithCapsOnCore endpointId receiver replyId c st).1 := by
  have h0 := endpointReceiveDualOnCore_savedRegsUnwritten endpointId receiver replyId c hInv
  unfold endpointReceiveDualWithCapsOnCore
  generalize endpointReceiveDualOnCore endpointId receiver replyId c st = r at h0
  obtain ⟨st1, r⟩ := r
  cases r with
  | error _ => exact h0
  | ok _ =>
    dsimp only
    repeat' split
    all_goals first
      | exact h0
      | (rename_i hU; exact h0.trans (receiveTransferCaps_savedRegsUnwritten h0.2 hU))

/-- The receive rendezvous' hand-off writes no saved register: the lend, then
the chain walk. -/
theorem applyReceiveRendezvousHandoff_savedRegsUnwritten {st st' : SystemState}
    {receiver dequeued : SeLe4n.ThreadId} {c : CoreId} (hInv : st.objects.invExt)
    (h : applyReceiveRendezvousHandoff st receiver dequeued c = .ok st') :
    savedRegsUnwritten st st' := by
  obtain ⟨stDon, hDon, rfl⟩ := applyReceiveRendezvousHandoff_ok_decompose _ _ _ _ _ h
  have h1 : savedRegsUnwritten st stDon := by
    unfold applyReceiveRendezvousDonation at hDon
    split at hDon
    · exact savedRegsUnwritten.of_applyRendezvousCallDonation hInv hDon
    · cases hDon; exact .refl hInv
  split
  · exact h1.trans (savedRegsUnwritten.of_propagate _ _ _ _ h1.2)
  · exact h1

/-! ### Reply -/

/-- The per-core reply writes no saved register: the caller is readied with the
reply as a pending message and woken, its reply frame is removed and it leaves
the server's reply waiters. -/
theorem endpointReplyOnCore_savedRegsUnwritten (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (c : CoreId) {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st (endpointReplyOnCore replier target msg c st).1 := by
  unfold endpointReplyOnCore
  split
  · exact .refl hInv
  split
  · exact .refl hInv
  · rename_i tcb hL
    split
    · split
      · exact .refl hInv
      · rename_i st1 hS
        have h1 := savedRegsUnwritten.of_storeTcbIpcStateAndMessage_fromTcb hInv hL hS
        have hW := h1.trans (savedRegsUnwritten.of_wakeThread st1 target c h1.2)
        split
        · exact hW.trans (savedRegsUnwritten.of_unlinkReplyWaiterOpt _ _ _ hW.2)
        · split
          · rename_i st2 hR
            have h2 := hW.trans (savedRegsUnwritten.of_removeCallerReplyFrame hW.2 hR)
            exact h2.trans (savedRegsUnwritten.of_unlinkReplyWaiterOpt _ _ _ h2.2)
          · exact .refl hInv
    · exact .refl hInv

/-- The reply's donation return: the resolved return, the returned context's
settle and the holder's deschedule. -/
theorem applyReplyDonationOnCore_savedRegsUnwritten {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {targetVtid : SeLe4n.ValidThreadId} {ownerHome : CoreId} (hInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st rid targetVtid ownerHome = .ok st') :
    savedRegsUnwritten st st' := by
  unfold applyReplyDonationOnCore at h
  dsimp only at h
  split at h
  · exact savedRegsUnwritten.of_popUnheldReplyHead hInv h
  · split at h
    · split at h
      · split at h
        · cases h
        · rename_i st1 hRet
          cases h
          have h1 := savedRegsUnwritten.of_returnDonatedSchedContextResolved hInv hRet
          exact h1.trans ((savedRegsUnwritten.of_settle _ _ _ h1.2).trans
            (savedRegsUnwritten.of_descheduleAt _ _ _
              (SchedContextOps.settleReturnedContext_objects_invExt _ _ _ h1.2)))
      · exact savedRegsUnwritten.of_keepDonatedSchedContextResolved hInv h
    · cases h

/-- The live reply writes no saved register: the reply leg, the donation
return and the chain walk from the recorded server. -/
theorem endpointReplyCrossCoreDispatch_savedRegsUnwritten (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (c : CoreId) {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st (endpointReplyCrossCoreDispatch replier target msg c st).1 := by
  have h0 := endpointReplyOnCore_savedRegsUnwritten replier target msg c hInv
  unfold endpointReplyCrossCoreDispatch
  generalize endpointReplyOnCore replier target msg c st = r at h0
  obtain ⟨st1, res⟩ := r
  cases res with
  | error _ => exact .refl hInv
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact .refl hInv
      | exact h0
      | exact h0.trans (savedRegsUnwritten.of_propagate _ _ _ _ h0.2)
      | (rename_i hD
         have h1 := h0.trans (applyReplyDonationOnCore_savedRegsUnwritten h0.2 hD)
         exact h1.trans (savedRegsUnwritten.of_propagate _ _ _ _ h1.2))
      | (rename_i hD
         exact h0.trans (applyReplyDonationOnCore_savedRegsUnwritten h0.2 hD))

theorem endpointReplyCrossCoreDispatchChecked_savedRegsUnwritten (ctx : LabelingContext)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId) {st : SystemState}
    (hInv : st.objects.invExt) :
    savedRegsUnwritten st (endpointReplyCrossCoreDispatchChecked ctx replier target msg c st).1 := by
  unfold endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch_savedRegsUnwritten _ _ _ _ hInv
  · exact .refl hInv

/-! ### ReplyRecv's donation legs -/

theorem replyRecvPopDonation_savedRegsUnwritten {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {st st' : SystemState} {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (hInv : st.objects.invExt) (h : replyRecvPopDonation rid target st = .ok (r, st')) :
    savedRegsUnwritten st st' := by
  unfold replyRecvPopDonation at h
  split at h
  · split at h
    · split at h
      · split at h
        · cases h
        · rename_i st1 hRet
          cases h
          have h1 := savedRegsUnwritten.of_returnDonatedSchedContextResolved hInv hRet
          exact h1.trans (savedRegsUnwritten.of_settle _ _ _ h1.2)
      · split at h
        · cases h
        · rename_i st1 hK
          cases h
          exact savedRegsUnwritten.of_keepDonatedSchedContextResolved hInv hK
    · cases h
  · split at h
    · cases h
    · rename_i st1 hPop
      cases h
      exact savedRegsUnwritten.of_popUnheldReplyHead hInv hPop

theorem replyRecvPostReceiveDonation_savedRegsUnwritten
    {tid recordedServer nextThread : SeLe4n.ThreadId} {serverCore : CoreId}
    {returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
      = .ok ((), st')) :
    savedRegsUnwritten st st' := by
  unfold replyRecvPostReceiveDonation at h
  split at h
  · split at h
    · split at h
      · cases h
      · rename_i st2 hD
        cases h
        have h1 := savedRegsUnwritten.of_applyRendezvousCallDonation hInv hD
        exact h1.trans (savedRegsUnwritten.of_propagate _ _ _ _ h1.2)
    · cases h
      exact savedRegsUnwritten.of_propagate _ _ _ _ hInv
  · rename_i holder
    have hH : savedRegsUnwritten st (replyRecvHolderDeschedule tid holder st) := by
      unfold replyRecvHolderDeschedule
      split
      · exact .refl hInv
      · exact savedRegsUnwritten.of_descheduleAt _ _ _ hInv
    split at h
    · split at h
      · cases h
      · rename_i st2 hD
        cases h
        have h1 := hH.trans (savedRegsUnwritten.of_applyRendezvousCallDonation hH.2 hD)
        exact h1.trans (savedRegsUnwritten.of_propagate _ _ _ _ h1.2)
    · cases h
      have hP := savedRegsUnwritten.of_descheduleAt st holder (placedCoreOf? st holder) hInv
      exact hP.trans (savedRegsUnwritten.of_propagate _ _ _ _ hP.2)

theorem applyReceiveLegPipHandoff_savedRegsUnwritten (st : SystemState)
    (receiver dequeued alreadyWalked : SeLe4n.ThreadId) (c : CoreId) (hInv : st.objects.invExt) :
    savedRegsUnwritten st (applyReceiveLegPipHandoff st receiver dequeued alreadyWalked c) := by
  unfold applyReceiveLegPipHandoff
  split
  · exact .refl hInv
  split
  · exact savedRegsUnwritten.of_propagate _ _ _ _ hInv
  · exact .refl hInv

/-! ### The threads the staging names -/

/-- **The send queue's head is held by no core**: it is blocked. -/
theorem offCoreFree_of_sendHead {e : CoreId} {st : SystemState} {epId : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} (hD : st.currentDequeuedUnique) (hQ : queueHeadBlockedConsistent st)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (h : (st.getEndpoint? epId).bind (·.sendQ.head) = some t) : offCoreFree e st t := by
  cases hE : st.getEndpoint? epId with
  | none => rw [hE] at h; cases h
  | some ep =>
    rw [hE] at h
    exact offCoreFree_of_notReady hD hRT hBNR fun x hx =>
      endpointWaiter_notReady (q := false) hQ hE (by simpa [endpointWaitQueue] using h) hx

/-- **A successful reply leg names a thread blocked on its reply**: the leg
refuses any other. -/
theorem endpointReplyOnCore_ok_target_notReady {replier target : SeLe4n.ThreadId}
    {msg : IpcMessage} {c : CoreId} {st : SystemState} {sgi : Option (CoreId × Concurrency.SgiKind)}
    (h : (endpointReplyOnCore replier target msg c st).2 = .ok sgi) :
    ∀ x, st.getTcb? target = some x → x.ipcState ≠ .ready := by
  obtain ⟨-, tcb, ep, ex, -, hL, hS, -⟩ := endpointReplyOnCore_ok_decompose _ _ _ _ _ h
  intro x hx
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr (lookupTcb_some_objects _ _ _ hL)] at hx
  cases hx; rw [hS]; intro h; cases h

theorem endpointReplyCrossCoreDispatch_ok_target_notReady {replier target : SeLe4n.ThreadId}
    {msg : IpcMessage} {c : CoreId} {st s1 : SystemState} {x : Option (CoreId × Concurrency.SgiKind)}
    (h : endpointReplyCrossCoreDispatch replier target msg c st = (s1, .ok x)) :
    ∀ y, st.getTcb? target = some y → y.ipcState ≠ .ready := by
  unfold endpointReplyCrossCoreDispatch at h
  revert h
  generalize hR : endpointReplyOnCore replier target msg c st = r
  obtain ⟨st1, res⟩ := r
  cases res with
  | error _ => intro h; cases h
  | ok sgi => intro _; exact endpointReplyOnCore_ok_target_notReady (sgi := sgi) (by rw [hR])

theorem endpointReplyCrossCoreDispatchChecked_ok_target_notReady {ctx : LabelingContext}
    {replier target : SeLe4n.ThreadId} {msg : IpcMessage} {c : CoreId} {st s1 : SystemState}
    {x : Option (CoreId × Concurrency.SgiKind)}
    (h : endpointReplyCrossCoreDispatchChecked ctx replier target msg c st = (s1, .ok x)) :
    ∀ y, st.getTcb? target = some y → y.ipcState ≠ .ready := by
  unfold endpointReplyCrossCoreDispatchChecked at h
  split at h
  · exact endpointReplyCrossCoreDispatch_ok_target_notReady h
  · cases h

/-! ### The arms -/

/-- WS-ZA ZA6.26: **the call arm writes only the woken receiver**: the checked
call writes no saved register, and the delivery's staging names the receive
queue's head at the entry's start, which is blocked there. -/
theorem callArm_savedRegsWrittenFree {ctx : LabelingContext} {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {payload : SendPayload} {ec e : CoreId}
    {st s1 : SystemState} {r : CapTransferSummary × Option (CoreId × Concurrency.SgiKind)}
    (n : Nat) (P : SyscallArmPremises st ec tid) (hRT : st.residentsHaveTcbs)
    (hBNR : st.blockedNotResident)
    (hCall : endpointCallCrossCoreDispatchChecked ctx epId tid payload ec st = (s1, .ok r)) :
    savedRegsWrittenFree e st st (Architecture.stageWokenDelivery s1
      ((st.getEndpoint? epId).bind (·.receiveQ.head)) n) := by
  have h1 := endpointCallCrossCoreDispatchChecked_savedRegsUnwritten ctx epId tid payload ec
    P.objInv
  rw [hCall] at h1
  exact h1.writtenFree.trans (stageWokenDelivery_savedRegsWrittenFree n h1.2 fun _ h =>
    offCoreFree_of_receiveHead P.dequeued P.queueHeads hRT hBNR h).1

/-- **The receive arm up to its caller's staging writes only the woken
sender**: the receive and its hand-off write no saved register, and the send's
completion names the send queue's head at the entry's start, which is blocked
there, so it is free of every core. -/
theorem receiveArmCompletion_savedRegsWrittenFree {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {replyId : Option SeLe4n.ReplyId} {ec e : CoreId}
    {base st s1 stDon : SystemState} {dequeued : SeLe4n.ThreadId} {summary : CapTransferSummary}
    {sgi : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (hHead : ∀ w, (st.getEndpoint? epId).bind (·.sendQ.head) = some w → offCoreFree e base w)
    (hRecv : endpointReceiveDualWithCapsOnCore epId tid replyId ec st
      = (s1, .ok (dequeued, summary, sgi)))
    (hHand : applyReceiveRendezvousHandoff s1 tid dequeued ec = .ok stDon) :
    savedRegsWrittenFree e base st
      stDon ∧
    stDon.objects.invExt := by
  have h1 := endpointReceiveDualWithCapsOnCore_savedRegsUnwritten epId tid replyId ec hInv
  rw [hRecv] at h1
  have h2 := h1.trans (applyReceiveRendezvousHandoff_savedRegsUnwritten h1.2 hHand)
  exact ⟨h2.writtenFree, h2.2⟩

/-- WS-ZA ZA6.26: **the receive arm writes only the woken sender and the
caller**: up to the caller's staging it writes only the woken sender
(`receiveArmCompletion_savedRegsWrittenFree`), and the delivered message is
staged into the caller, the executing core's current thread. -/
theorem receiveArm_savedRegsWrittenFree {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {replyId : Option SeLe4n.ReplyId} {ec : CoreId}
    {base st s1 stDon : SystemState} {dequeued : SeLe4n.ThreadId} {summary : CapTransferSummary}
    {sgi : Option (CoreId × Concurrency.SgiKind)} (n : Nat) (hInv : st.objects.invExt)
    (hHead : ∀ w, (st.getEndpoint? epId).bind (·.sendQ.head) = some w → offCoreFree ec base w)
    (hCaller : offCoreFree ec base tid)
    (hRecv : endpointReceiveDualWithCapsOnCore epId tid replyId ec st
      = (s1, .ok (dequeued, summary, sgi)))
    (hHand : applyReceiveRendezvousHandoff s1 tid dequeued ec = .ok stDon) :
    savedRegsWrittenFree ec base st (Architecture.stageDeliveredMessage
      stDon
      tid n) := by
  obtain ⟨w1, i1⟩ := receiveArmCompletion_savedRegsWrittenFree (e := ec) hInv hHead hRecv hHand
  obtain ⟨k, -⟩ := stageDeliveredMessage_savedRegsKeptExcept _ tid n i1
  exact w1.trans (.of_kept k fun _ h => h ▸ hCaller)

/-- WS-ZA ZA6.26: **the fault reply writes only the faulted thread**: the reply
chain writes no saved register and refuses a thread not blocked on its reply, so
the restart frame names a thread blocked at the entry's start. -/
theorem faultReplyOnCore_savedRegsWrittenFree {replier faulted : SeLe4n.ThreadId}
    {mi : MessageInfo} {regs : Array SeLe4n.RegValue} {ec e : CoreId} {st s' : SystemState}
    {x : Architecture.FaultReplyOutcome × Option (CoreId × Concurrency.SgiKind)}
    (hD : st.currentDequeuedUnique) (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (hInv : st.objects.invExt) (h : faultReplyOnCore replier faulted mi regs ec st = (s', .ok x)) :
    savedRegsWrittenFree e st st s' := by
  unfold faultReplyOnCore at h
  split at h
  · cases h
  split at h
  · cases h
  dsimp only at h
  revert h
  generalize hR : endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty ec st = r
  obtain ⟨s1, res⟩ := r
  cases res with
  | error _ => intro h; cases h
  | ok sgi =>
    intro h
    cases h
    have hB := endpointReplyCrossCoreDispatch_ok_target_notReady hR
    have h1 := endpointReplyCrossCoreDispatch_savedRegsUnwritten replier faulted IpcMessage.empty
      ec hInv
    rw [hR] at h1
    refine h1.writtenFree.trans (.of_kept (W := (· = faulted)) ?_ fun _ e =>
      e ▸ offCoreFree_of_notReady hD hRT hBNR hB)
    unfold faultReplyApplyOnCore
    split
    · exact .updateTcb_written _ _ _ h1.2 rfl
    · unfold faultAbandonOnCore
      exact (savedRegsUnwritten.of_removeRunnableOnCore _ _ _ h1.2).kept.trans
        (.updateTcb _ _ _ (removeRunnableOnCore_objects_invExt _ _ _ h1.2) fun _ => rfl)

/-- WS-ZA ZA6.26: **the reply arm writes only the answered caller**: the fault
reply's restart frame or the delivered reply's staging, each into a thread the
reply leg found blocked on its reply at the entry's start. -/
theorem replyTransferOnCoreChecked_savedRegsWrittenFree {ctx : LabelingContext}
    {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo} {regs : Array SeLe4n.RegValue}
    {msg : IpcMessage} {grant : Bool} {ec e : CoreId} {st st' : SystemState}
    (hD : st.currentDequeuedUnique) (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (hInv : st.objects.invExt)
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant ec st = .ok ((), st')) :
    savedRegsWrittenFree e st st st' := by
  unfold replyTransferOnCoreChecked at h
  split at h
  · revert h
    generalize hF : faultReplyOnCore replier callerTid mi regs ec st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h; cases h
    | ok _ => intro h; cases h; exact faultReplyOnCore_savedRegsWrittenFree hD hRT hBNR hInv hF
  · revert h
    generalize hR : endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg ec st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h; cases h
    | ok _ =>
      intro h
      simp only [] at h
      cases hX : replyTransferCaps st replier callerTid grant s with
      | error _ => rw [hX] at h; cases h
      | ok p =>
        obtain ⟨summary, sX⟩ := p
        rw [hX] at h
        cases h
        have h1 := endpointReplyCrossCoreDispatchChecked_savedRegsUnwritten ctx replier callerTid
          msg ec hInv
        rw [hR] at h1
        have h2 := h1.trans (receiveTransferCaps_savedRegsUnwritten h1.2 hX)
        exact h2.writtenFree.trans (.of_kept (stageDeliveredMessage_savedRegsKeptExcept sX
          callerTid summary.capInfo h2.2).1 fun _ e => e ▸ offCoreFree_of_notReady hD hRT hBNR
            (endpointReplyCrossCoreDispatchChecked_ok_target_notReady hR))

/-- Answering the `.replyRecv` caller writes the saved registers of that caller
only: the staging of its delivered message, or the fault outcome (a restart frame
into the faulted thread, an abandon that writes no register). -/
theorem replyRecvAnswerCaller_savedRegsKeptExcept
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState)
    (prevCaller : SeLe4n.ThreadId) (capInfo : Nat) (hInv : st.objects.invExt) :
    savedRegsKeptExcept (· = prevCaller) st (replyRecvAnswerCaller answer st prevCaller capInfo) ∧
      (replyRecvAnswerCaller answer st prevCaller capInfo).objects.invExt := by
  cases answer with
  | none => exact stageDeliveredMessage_savedRegsKeptExcept st prevCaller capInfo hInv
  | some outcome =>
    refine ⟨?_, replyRecvAnswerCaller_preserves_objects_invExt _ st prevCaller _ hInv⟩
    show savedRegsKeptExcept (· = prevCaller) st (faultReplyApplyOnCore st prevCaller outcome)
    unfold faultReplyApplyOnCore
    split
    · exact .updateTcb_written _ _ _ hInv rfl
    · unfold faultAbandonOnCore
      exact (savedRegsUnwritten.of_removeRunnableOnCore _ _ _ hInv).kept.trans
        (.updateTcb _ _ _ (removeRunnableOnCore_objects_invExt _ _ _ hInv) fun _ => rfl)

/-- **seL4 `receiveIPC`'s return writes no saved registers**: it clears two
binding codes and a context's thread link (WS-SX SX8.2). -/
theorem savedRegsUnwritten.receiveReturn (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    savedRegsUnwritten st (receiveReturnSchedContext blocks st tid) :=
  ⟨fun t _ => by
    unfold SystemState.savedRegs SystemState.getTcb?
    rcases receiveReturnSchedContext_objects blocks st tid hInv t.toObjId with
      e | ⟨y, hy, e⟩ | ⟨sc, sc', hs, e⟩
    · rw [e]
    · rw [e, hy] <;> rfl
    · rw [e, hs],
   receiveReturnSchedContext_objects_invExt blocks st tid hInv⟩

/-- WS-ZA ZA6.26: **the reply-and-receive writes only the answered caller and
the woken sender**: its legs write no saved register; the reply's staging names
the caller the reply leg found blocked on its reply, and the send's completion
names the send queue's head after the reply leg, the donation pop and the reply
leg's capability transfer, which write no endpoint, so the head the entry began from, blocked there. -/
theorem endpointReplyRecvOnCore_savedRegsWrittenFree {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId}
    {msg : IpcMessage} {grant : Bool} {ec e : CoreId}
    {st st' : SystemState} {summary : CapTransferSummary}
    {answer : Option Architecture.FaultReplyOutcome}
    (hD : st.currentDequeuedUnique) (hQ : queueHeadBlockedConsistent st)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident) (hInv : st.objects.invExt)
    (h : endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg grant ec st
      = .ok (summary, st')) :
    savedRegsWrittenFree e st st st' ∧ st'.objects.invExt := by
  unfold endpointReplyRecvAnsweringOnCore at h
  dsimp only at h
  have h0 := endpointReplyOnCore_savedRegsUnwritten tid prevCaller msg ec hInv
  have hB0 := endpointReplyOnCore_endpoint_backward tid prevCaller msg ec st hInv
  revert h h0 hB0
  generalize hR : endpointReplyOnCore tid prevCaller msg ec st = r1
  obtain ⟨st1, res1⟩ := r1
  cases res1 with
  | error _ => intro h; cases h
  | ok sgi =>
  intro h h0 hB0
  have hPC := endpointReplyOnCore_ok_target_notReady (sgi := sgi) (by rw [hR])
  try dsimp only at h
  split at h
  · cases h
  rename_i ret st1q hPop
  obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer st tid prevCaller grant st1q
  rw [hX] at h
  try dsimp only at h
  have hXU := hX
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hXU
  have h1q := h0.trans (replyRecvPopDonation_savedRegsUnwritten h0.2 hPop)
  have h1 := h1q.trans (receiveTransferCaps_savedRegsUnwritten h1q.2 hXU)
  have hB1 : ∀ (o : SeLe4n.ObjId) (ep : Endpoint), st1p.objects[o]? = some (.endpoint ep) →
      st1.objects[o]? = some (.endpoint ep) := fun o ep hx =>
    (replyRecvPopDonation_frame h0.2 hPop).1 o ep
      ((receiveTransferCaps_ipcFrame h1q.2 hXU).1 o ep hx)
  -- seL4-MCS `receiveIPC`'s `maybeReturnSchedContext`, before the receive leg.
  have h1r := h1.trans (savedRegsUnwritten.receiveReturn true st1p tid h1.2)
  have h2v := endpointReceiveDualWithCapsOnCore_savedRegsUnwritten epId tid (some rid)
    ec h1r.2
  revert h h2v
  generalize endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
    (receiveReturnSchedContext true st1p tid) = r2
  obtain ⟨st2, res2⟩ := r2
  cases res2 with
  | error _ => intro h; cases h
  | ok q =>
  obtain ⟨nextThread, summ, _⟩ := q
  intro h h2v
  try dsimp only at h
  split at h
  · cases h
  rename_i st3 hPost
  cases h
  have h2 := h1r.trans h2v
  have h3 := h2.trans (replyRecvPostReceiveDonation_savedRegsUnwritten h2.2 hPost)
  have h4 := h3.trans (applyReceiveLegPipHandoff_savedRegsUnwritten st3 tid nextThread
    ((recordedReplyServer? st prevCaller).getD tid) ec h3.2)
  obtain ⟨k5, i5⟩ := replyRecvAnswerCaller_savedRegsKeptExcept answer _ prevCaller _ h4.2
  exact ⟨h4.writtenFree.trans (.of_kept k5 fun _ e =>
    e ▸ offCoreFree_of_notReady hD hRT hBNR hPC), i5⟩

end SeLe4n.Kernel
