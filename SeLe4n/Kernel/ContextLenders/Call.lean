-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Stage
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.Operations.CallLendLabel

/-! # The cross-core Call keeps the lenders' flow

WS-SX SX8.  seL4's `sendIPC` for a Call: the rendezvous (`endpointCallOnCore`,
which links the caller on the reply object its server stashed), the capability
transfer, then — where the call links a reply and the lend is admitted — the
context's donation to the passive server (`donateSchedContext`, a frame
pushed with the caller as its lender), the replenishment migration and the
priority walk.  The fault delivery and the syscall's `.call` arm both run it.

The donation reads the chain facts at the state the rendezvous leaves
(`LendersPremises`), as `Stage.lean` describes; the lend admission
(`callLendAdmits`) is read on the state the call starts from, which holds the
caller's binding unchanged (`endpointCallWithCapsOnCore_sameSchedContextBindings`). -/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace chainObjectsKept

/-- A capability transfer writes CNodes and thread records only. -/
theorem receiveTransferCaps {req : Option (Capability × Array SeLe4n.CPtr)}
    {endpointId : Option SeLe4n.ObjId} {target? : Option (TCB × Option CSpaceAddr)}
    {st st' : SystemState} {summary : CapTransferSummary} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.receiveTransferCaps req endpointId target? st = .ok (summary, st')) :
    chainObjectsKept st st' := by
  have key : ∀ x : SeLe4n.ObjId, ∀ o : KernelObject, st'.objects[x]? = some o →
      (∀ cn, o ≠ .cnode cn) → (∀ t, o ≠ .tcb t) → st.objects[x]? = some o := by
    intro x o hx hCn hT
    rcases receiveTransferCaps_object_cases x hInv h with
      (e | ⟨_, cn', -, h2, -⟩ | ⟨_, t', -, h2, -⟩) | ⟨_, -, -, -, cn', h2⟩
    · rw [← e]; exact hx
    · rw [h2] at hx; cases hx; exact absurd rfl (hCn cn')
    · rw [h2] at hx; cases hx; exact absurd rfl (hT t')
    · rw [h2] at hx; cases hx; exact absurd rfl (hCn cn')
  refine chainObjectsKept.of_words (fun x r hx => key x _ hx (fun _ h => by cases h) (fun _ h => by cases h))
    (fun x sc hx => key x _ hx (fun _ h => by cases h) (fun _ h => by cases h)) (fun x => ?_)
  rcases receiveTransferCaps_object_cases x hInv h with
    (e | ⟨_, _, h1, h2, -⟩ | ⟨t, t', h1, h2, hW⟩) | ⟨_, -, -, ⟨_, h1⟩, _, h2⟩
  · rw [e]
  · rw [h1, h2]; rfl
  · rw [h1, h2]
    show (t'.scBindingScCode, t'.scBindingOwnerCode, 0, 0) = (t.scBindingScCode, t.scBindingOwnerCode, 0, 0)
    have a := congrArg TCB.scBindingScCode hW
    have b := congrArg TCB.scBindingOwnerCode hW
    simp only [TCB.withoutLinks] at a b
    rw [a, b]
  · rw [h1, h2]; rfl

/-- The priority walk writes thread records and the scheduler only. -/
theorem propagatePipChainCrossCore (st : SystemState) (t : SeLe4n.ThreadId) (ec : CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    chainObjectsKept st (PriorityInheritance.propagatePipChainCrossCore st t ec fuel).1 := by
  have key : ∀ x : SeLe4n.ObjId, ∀ o : KernelObject,
      (PriorityInheritance.propagatePipChainCrossCore st t ec fuel).1.objects[x]? = some o →
      (∀ t, o ≠ .tcb t) → st.objects[x]? = some o := by
    intro x o hx hT
    rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st t ec hInv x with
      e | ⟨_, post, -, hPost, -⟩
    · rw [← e]; exact hx
    · rw [hPost] at hx; cases hx; exact absurd rfl (hT post)
  refine chainObjectsKept.of_words (fun x r hx => key x _ hx (fun _ h => by cases h))
    (fun x sc hx => key x _ hx (fun _ h => by cases h)) (fun x => ?_)
  rcases PriorityInheritance.propagatePipChainCrossCore_keepsScBindingAt fuel st t ec hInv x with
    e | ⟨pre, post, h1, h2, hS, hO⟩
  · rw [e]
  · rw [h1, h2]; simp only [objBindingWords, hS, hO]

end chainObjectsKept

/-- The replenishment migration moves release links only. -/
theorem LendersStage.migrateSchedContextReplenishment {ctx : LabelingContext} (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) :
    LendersStage ctx st (_root_.SeLe4n.Kernel.migrateSchedContextReplenishment st scId fromCore toCore) :=
  of_viewsAgree (contextStackViewsAgree_of_objectsAgreeOffReleaseLinks
    (migrateSchedContextReplenishment_agree st scId fromCore toCore))

/-- **The call donation carries equal lending labels** where the receiver it
lends to carries the caller's label: the one lend is `donateSchedContext`'s
push, and the caller carries the label of the context it holds (the binding
clause), so the receiver does too. -/
theorem applyCallDonation_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st st' : SystemState} {callerV receiverV : SeLe4n.ValidThreadId}
    (hP : LendersPremises st) (hInv : lendingLabelsEqual ctx st)
    (hRecv : ∀ rT : TCB, lookupTcb st receiverV.val = some rT →
      ctx.threadLabelOf receiverV.val = ctx.threadLabelOf callerV.val)
    (h : _root_.SeLe4n.Kernel.applyCallDonation st callerV receiverV = .ok st') :
    lendingLabelsEqual ctx st' := by
  unfold _root_.SeLe4n.Kernel.applyCallDonation at h
  dsimp only at h
  split at h
  · cases h; exact hInv
  · split at h
    · split at h
      · cases h; exact hInv
      · rename_i callerTcb hC
        split at h
        · rename_i s hS
          split at h
          · cases h
          · rename_i st1 hD
            cases h
            exact donateSchedContext_preserves_lendingLabelsEqual hP.invExt hP.chain hP.linkage
              hInv ((hRecv _ (by assumption)).trans
                (hInv.2.bound (lookupTcb_some_objects _ _ _ hC) hS)) hD
        · cases h; exact hInv
    all_goals (cases h; exact hInv)

/-- And its cross-core form: the donation, then the replenishment migration. -/
theorem applyCallDonationOnCore_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st st' : SystemState} {callerV receiverV : SeLe4n.ValidThreadId} {donorHome doneeHome : CoreId}
    (hP : LendersPremises st) (hInv : lendingLabelsEqual ctx st)
    (hRecv : ∀ rT : TCB, lookupTcb st receiverV.val = some rT →
      ctx.threadLabelOf receiverV.val = ctx.threadLabelOf callerV.val)
    (h : _root_.SeLe4n.Kernel.applyCallDonationOnCore st callerV receiverV donorHome doneeHome
      = .ok st') :
    lendingLabelsEqual ctx st' := by
  obtain ⟨st1, hDon, hArm⟩ := applyCallDonationOnCore_ok_decompose _ _ _ _ _ _ h
  have h1 := applyCallDonation_preserves_lendingLabelsEqual hP hInv hRecv hDon
  rcases hArm with ⟨_, rfl⟩ | ⟨scId, _, rfl⟩
  · exact h1
  · exact LendersStage.migrateSchedContextReplenishment _ _ _ _ h1

/-- **The rendezvous and the capability transfer carry the lenders' flow**:
the rendezvous's one caller link is on a free reply
(`endpointCallOnCore_preserves_lendingLabelsEqual`), and the transfer writes
CNodes and thread records. -/
theorem endpointCallWithCapsOnCore_preserves_lendingLabelsEqual {ctx : LabelingContext}
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (core : CoreId) (st : SystemState) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hFlow : lendingLabelsEqual ctx st) :
    lendingLabelsEqual ctx (endpointCallWithCapsOnCore endpointId caller payload core st).1 := by
  have h1 := endpointCallOnCore_preserves_lendingLabelsEqual (endpointId := endpointId)
    (caller := caller) (payload := payload) (core := core) hInv hChain hFlow
  have hI1 := endpointCallOnCore_preserves_objects_invExt endpointId caller payload core st hInv
  unfold endpointCallWithCapsOnCore
  cases hC : endpointCallOnCore endpointId caller payload core st with
  | mk st1 r =>
    rw [hC] at h1 hI1
    cases r with
    | error e => exact h1
    | ok sgi =>
      dsimp only
      split
      · exact h1
      · split
        · split
          · exact h1
          · rename_i hT
            exact LendersStage.of_kept (chainObjectsKept.receiveTransferCaps hI1 hT) h1
        · exact h1

/-- **The full cross-core Call carries equal lending labels**: the rendezvous
and the transfer, then the donation where the call links a reply, then the
replenishment migration and the priority walk.  The donation lends to the
receive queue's head at the state the call starts from, a thread blocked
receiving on the endpoint, so carrying the endpoint's label
(`blockedReceiverLabelsEqual`, SX11), which the caller's own gate equals. -/
theorem endpointCallCrossCoreDispatch_preserves_lendingLabelsEqual {ctx : LabelingContext}
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState) (lend : Bool)
    (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hMid : LendersPremises (endpointCallWithCapsOnCore endpointId caller payload executingCore st).1)
    (hWait : blockedReceiverLabelsEqual ctx st) (hQ : queueHeadBlockedConsistent st)
    (hGate : ctx.threadLabelOf caller = ctx.endpointLabelOf endpointId)
    (hFlow : lendingLabelsEqual ctx st) :
    lendingLabelsEqual ctx (endpointCallCrossCoreDispatch endpointId caller payload executingCore st
      lend).1 := by
  have h1 := endpointCallWithCapsOnCore_preserves_lendingLabelsEqual endpointId caller payload
    executingCore st hInv hChain hFlow
  have hFrame := endpointCallWithCapsOnCore_sameSchedContextBindings endpointId caller payload
    executingCore st hInv
  unfold endpointCallCrossCoreDispatch
  cases hWc : endpointCallWithCapsOnCore endpointId caller payload executingCore st with
  | mk st' res =>
    rw [hWc] at h1 hFrame hMid
    simp only at h1 hFrame hMid
    cases res with
    | error e => exact h1
    | ok pair =>
      obtain ⟨summary, sgi⟩ := pair
      simp only []
      split
      · rename_i receiverTid hRecvTid
        split
        · split
          · rename_i callerV receiverV hCV hRV
            split
            · exact h1
            · rename_i st'' hDon
              rcases applyCallDonationOnCoreWhen_cases hDon with ⟨-, hDon⟩ | ⟨_, rfl⟩
              · have h2 := applyCallDonationOnCore_preserves_lendingLabelsEqual hMid h1
                  (fun rT' hRLook' => by
                    obtain ⟨rTcb, hRObj, -⟩ :=
                      hFrame receiverV.val rT' (lookupTcb_some_objects st' receiverV.val rT' hRLook')
                    have hRLook : lookupTcb st receiverV.val = some rTcb :=
                      lookupTcb_of_objects_of_not_reserved st receiverV.val rTcb hRObj
                        (lookupTcb_some_not_reserved st' receiverV.val rT' hRLook')
                    have hCallerEq : callerV.val = caller :=
                      SeLe4n.ThreadId.toValid?_some_val_eq caller callerV hCV
                    have hRecvEq : receiverV.val = receiverTid :=
                      SeLe4n.ThreadId.toValid?_some_val_eq receiverTid receiverV hRV
                    cases hEp : st.getEndpoint? endpointId with
                    | none => rw [hEp] at hRecvTid; exact absurd hRecvTid (by simp)
                    | some ep =>
                      rw [hEp] at hRecvTid
                      simp only at hRecvTid
                      have hEpObj := (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
                      rw [hRecvEq] at hRLook ⊢
                      rw [hCallerEq, hGate]
                      exact hWait receiverTid rTcb endpointId hRLook
                        ((hQ endpointId ep receiverTid rTcb hEpObj
                          (lookupTcb_some_objects st receiverTid rTcb hRLook)).1 hRecvTid)) hDon
                have hI2 := applyCallDonationOnCore_preserves_objects_invExt _ _ _ _ _ _
                  hMid.invExt hDon
                exact LendersStage.of_kept (chainObjectsKept.propagatePipChainCrossCore _ _ _ _ hI2) h2
              · exact LendersStage.of_kept
                  (chainObjectsKept.propagatePipChainCrossCore _ _ _ _ hMid.invExt) h1
          all_goals exact h1
        · exact h1
      · exact h1

/-- **The flow-checked Call** (the syscall's `.call` arm): a refused gate
returns the state, and a passed one runs the Call under the admission read on
the state it starts from. -/
theorem endpointCallCrossCoreDispatchChecked_preserves_lendingLabelsEqual {ctx : LabelingContext}
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hMid : LendersPremises (endpointCallWithCapsOnCore endpointId caller payload executingCore st).1)
    (hWait : blockedReceiverLabelsEqual ctx st) (hQ : queueHeadBlockedConsistent st)
    (hFlow : lendingLabelsEqual ctx st) :
    lendingLabelsEqual ctx (endpointCallCrossCoreDispatchChecked ctx endpointId caller payload
      executingCore st).1 := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · rename_i hG
    exact endpointCallCrossCoreDispatch_preserves_lendingLabelsEqual endpointId caller payload
      executingCore st _ hInv hChain hMid hWait hQ
      (endpointFlowGate_implies_eq ctx endpointId _ _ hG) hFlow
  · exact hFlow

/-- **The rendezvous lend carries the lenders' flow**, lent or refused: lent, it
is the call donation, whose donor flows to every context it holds. -/
theorem applyRendezvousCallDonation_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st st' : SystemState} {receiver donor : SeLe4n.ThreadId} {lend : Bool}
    (hP : LendersPremises st) (hInv : lendingLabelsEqual ctx st)
    (hRecv : lend = true → ctx.threadLabelOf receiver = ctx.threadLabelOf donor)
    (h : applyRendezvousCallDonation st receiver donor lend = .ok st') :
    lendingLabelsEqual ctx st' := by
  unfold applyRendezvousCallDonation at h
  split at h
  · rename_i donorV receiverV hD hR
    have hEq : donorV.val = donor := SeLe4n.ThreadId.toValid?_some_val_eq donor donorV hD
    have hEqR : receiverV.val = receiver := SeLe4n.ThreadId.toValid?_some_val_eq receiver receiverV hR
    rcases applyCallDonationOnCoreWhen_cases h with ⟨hL, h⟩ | ⟨_, rfl⟩
    · exact applyCallDonationOnCore_preserves_lendingLabelsEqual hP hInv
        (fun _ _ => by rw [hEq, hEqR]; exact hRecv hL) h
    · exact hInv
  · cases h

/-- And the receive's guarded form: a receive that dequeued no `Call` lends
nothing, and a dequeued `Call` lends only the context the donation resolves
(`callDonationSchedContext?`), so the flow is asked of that context alone. -/
theorem applyReceiveRendezvousDonation_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st st' : SystemState} {receiver dequeued : SeLe4n.ThreadId} {lend : Bool}
    (hP : LendersPremises st) (hInv : lendingLabelsEqual ctx st)
    (hRecv : lend = true → rendezvousDequeuedCall st dequeued = true →
      ∀ s, callDonationSchedContext? st dequeued receiver = some s →
      ctx.threadLabelOf receiver = ctx.threadLabelOf dequeued)
    (h : applyReceiveRendezvousDonation st receiver dequeued lend = .ok st') :
    lendingLabelsEqual ctx st' := by
  cases hS : callDonationSchedContext? st dequeued receiver with
  | none =>
    cases hDV : dequeued.toValid? with
    | none =>
      unfold applyReceiveRendezvousDonation applyRendezvousCallDonation at h
      split at h
      · simp only [hDV, reduceCtorEq] at h
      · cases h; exact hInv
    | some dV =>
      cases hRV : receiver.toValid? with
      | none =>
        unfold applyReceiveRendezvousDonation applyRendezvousCallDonation at h
        split at h
        · simp only [hDV, hRV, reduceCtorEq] at h
        · cases h; exact hInv
      | some rV =>
        rw [applyReceiveRendezvousDonation_of_no_donation st receiver dequeued dV rV hDV hRV hS] at h
        cases h; exact hInv
  | some s =>
    unfold applyReceiveRendezvousDonation at h
    split at h
    · rename_i hCall
      exact applyRendezvousCallDonation_preserves_lendingLabelsEqual hP hInv
        (fun hL => hRecv hL hCall s hS) h
    · cases h; exact hInv

/-- **The receive rendezvous' hand-off carries the lenders' flow**: the lend,
then the priority walk. -/
theorem applyReceiveRendezvousHandoff_preserves_lendingLabelsEqual {ctx : LabelingContext}
    {st st' : SystemState} {receiver dequeued : SeLe4n.ThreadId} {ec : CoreId} {lend : Bool}
    (hP : LendersPremises st) (hInv : lendingLabelsEqual ctx st)
    (hRecv : lend = true → rendezvousDequeuedCall st dequeued = true →
      ∀ s, callDonationSchedContext? st dequeued receiver = some s →
      ctx.threadLabelOf receiver = ctx.threadLabelOf dequeued)
    (h : applyReceiveRendezvousHandoff st receiver dequeued ec lend = .ok st') :
    lendingLabelsEqual ctx st' := by
  obtain ⟨stDon, hDon, rfl⟩ := applyReceiveRendezvousHandoff_ok_decompose _ _ _ _ _ h
  have h1 := applyReceiveRendezvousDonation_preserves_lendingLabelsEqual hP hInv hRecv hDon
  have hI := applyReceiveRendezvousDonation_preserves_objects_invExt _ _ _ _ hP.invExt hDon
  split
  · exact LendersStage.of_kept (chainObjectsKept.propagatePipChainCrossCore _ _ _ _ hI) h1
  · exact h1

/-- **The per-core receive with its capability transfer carries the lenders'
flow**: the receive's one caller link is on a free reply
(`endpointReceiveDualOnCore_preserves_lendingLabelsEqual`), and the transfer
writes CNodes and thread records. -/
theorem endpointReceiveDualWithCapsOnCore_preserves_lendingLabelsEqual {ctx : LabelingContext}
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (core : CoreId) (st : SystemState) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st) (hFlow : lendingLabelsEqual ctx st) :
    lendingLabelsEqual ctx
      (endpointReceiveDualWithCapsOnCore endpointId receiver replyId core st).1 := by
  have h1 := endpointReceiveDualOnCore_preserves_lendingLabelsEqual (endpointId := endpointId)
    (receiver := receiver) (replyId := replyId) (core := core) hInv hChain hFlow
  have hI1 := endpointReceiveDualOnCore_preserves_objects_invExt endpointId receiver replyId core
    st hInv
  unfold endpointReceiveDualWithCapsOnCore
  cases hC : endpointReceiveDualOnCore endpointId receiver replyId core st with
  | mk st1 r =>
    rw [hC] at h1 hI1
    cases r with
    | error e => exact h1
    | ok p =>
      obtain ⟨_, _⟩ := p
      dsimp only
      split
      · exact h1
      · split
        · exact h1
        · rename_i hT
          exact LendersStage.of_kept (chainObjectsKept.receiveTransferCaps hI1 hT) h1

/-- **The per-core send writes no reply object and no context**: the
rendezvous pops the receiver, completes its receive and wakes it; the block
enqueues the sender, blocks it and deschedules it. -/
theorem chainObjectsKept.endpointSendDualOnCore (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload) (core : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) :
    chainObjectsKept st (_root_.SeLe4n.Kernel.endpointSendDualOnCore endpointId sender payload
      core st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointSendDualOnCore
  split
  · split
    · split
      · exact refl _
      · split
        · exact refl _
        · rename_i receiver _ st1 hPop
          have hK1 := endpointQueuePopHead hInv hPop
          have hI1 := endpointQueuePopHead_preserves_objects_invExt _ _ _ _ _ _ hInv hPop
          split
          · exact refl _
          · rename_i st2 hS2
            have hK2 := hK1.trans (storeTcbReceiveComplete hI1 hS2)
            have hI2 := storeTcbReceiveComplete_preserves_objects_invExt _ _ _ _ hI1 hS2
            exact hK2.trans (wakeThread st2 receiver core hI2)
    · split
      · exact refl _
      · rename_i st1 hE
        have hK1 := endpointQueueEnqueue hInv hE
        have hI1 := endpointQueueEnqueue_preserves_objects_invExt _ _ _ _ _ hInv hE
        split
        · exact refl _
        · rename_i st2 hS2
          exact (hK1.trans (storeTcbIpcStateAndMessage hI1 hS2)).trans
            ((removeRunnableOnCore _ sender core).trans (recordSendCap _ sender _ _ _))
  · split <;> exact refl _

/-- **The flow-checked send carries the lenders' flow**: it lends nothing and
links no caller. -/
theorem endpointSendCrossCoreDispatchChecked_lendersStage {ctx : LabelingContext}
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (core : CoreId) (st : SystemState) (hInv : st.objects.invExt) :
    LendersStage ctx st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender payload core st).1 := by
  have hK := chainObjectsKept.endpointSendDualOnCore endpointId sender payload core st hInv
  have hI1 := endpointSendDualOnCore_preserves_objects_invExt endpointId sender payload core st hInv
  unfold endpointSendCrossCoreDispatchChecked
  split
  · unfold endpointSendDualWithCapsOnCore
    cases hC : _root_.SeLe4n.Kernel.endpointSendDualOnCore endpointId sender payload core st with
    | mk st1 r =>
      rw [hC] at hK hI1
      cases r with
      | error e => exact LendersStage.of_kept hK
      | ok sgi =>
        dsimp only
        split
        · exact LendersStage.of_kept hK
        · split
          · split
            · exact LendersStage.of_kept hK
            · rename_i hT
              exact LendersStage.of_kept (hK.trans (chainObjectsKept.receiveTransferCaps hI1 hT))
          · exact LendersStage.of_kept hK
  · exact LendersStage.refl _

end SeLe4n.Kernel
