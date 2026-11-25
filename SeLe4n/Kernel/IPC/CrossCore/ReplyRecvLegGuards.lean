/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyHeldInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvUnlinkedTakeInPlace

/-!
# The reply leg's guards, one family over every pop arm

WS-SX SX25.1.  The reply-receive's reply leg ends in one of five arms: no pop
(the caller recorded the server and lent it nothing), the donated pop, the held
pop, the unheld pop, or no pop on a reply linked to nothing.  Each receive leg
the composed path runs after it (block, take, donating take) reads a guard on
the state the reply leg leaves, and checks it on the pre-state.  The guards are
carried by one shape per receive leg: the reply's writes, then the pop's, which
leave every thread but the pop's own (the caller and the context's holder) as it
was (`returnDonatedSchedContextInPlace_tcbAt`,
`keepDonatedSchedContextInPlace_tcbAt`, `returnUnheldSchedContextInPlace_tcbAt`)
and write nothing else a guard reads (`popFrame`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section ReplyLegGuards

/-- **The donated pop leaves every thread but its two as it was**: the context's
holder and its recipient. -/
theorem returnDonatedSchedContextInPlace_tcbAt (st : SystemState)
    (holder owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) {x : SeLe4n.ObjId} {t : TCB}
    (hxo : x ≠ owner.toObjId) (hxh : x ≠ holder.toObjId)
    (hX : st.objects[x]? = some (.tcb t)) :
    (returnDonatedSchedContextInPlace st holder owner scId).objects[x]? = some (.tcb t) := by
  unfold returnDonatedSchedContextInPlace
  split
  · exact hX
  · split
    · exact hX
    · split
      · exact hX
      · split
        · exact hX
        · split
          · exact hX
          · dsimp only
            rw [markKeyChangeParts_objects, markCandidacyGainFor_objects, markKeyChangeParts_objects,
              markCandidacyGainFor_objects]
            rw [objects_updateTcb_ne _ _ _ (by
                split <;> repeat (first
                  | assumption
                  | apply updateTcb_noResizeDue
                  | apply modifyObject_noResizeDue
                  | apply updateSchedContext_noResizeDue)) _ hxh,
              objects_updateTcb_ne _ _ _ (by
                  split <;> repeat (first
                    | assumption
                    | apply updateTcb_noResizeDue
                    | apply modifyObject_noResizeDue
                    | apply updateSchedContext_noResizeDue)) _ hxo]
            split <;> repeat (first
                | assumption
                | apply modifyReply_tcbAt
                | apply updateSchedContext_tcbAt
                | apply modifyObject_noResizeDue
                | apply updateSchedContext_noResizeDue)

/-- **The held pop leaves every thread but the holder as it was.** -/
theorem keepDonatedSchedContextInPlace_tcbAt (st : SystemState)
    (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) {x : SeLe4n.ObjId} {t : TCB} (hxh : x ≠ holder.toObjId)
    (hX : st.objects[x]? = some (.tcb t)) :
    (keepDonatedSchedContextInPlace st holder scId).objects[x]? = some (.tcb t) := by
  unfold keepDonatedSchedContextInPlace
  split
  · exact hX
  · split
    · exact hX
    · split
      · exact hX
      · split
        · exact hX
        · dsimp only
          rw [objects_updateTcb_ne _ _ _ (by
              split <;> repeat (first
                | assumption
                | apply updateTcb_noResizeDue
                | apply modifyObject_noResizeDue
                | apply updateSchedContext_noResizeDue)) _ hxh]
          split <;> repeat (first
              | assumption
              | apply modifyReply_tcbAt
              | apply updateSchedContext_tcbAt
              | apply modifyObject_noResizeDue
              | apply updateSchedContext_noResizeDue)

/-- **The take's guard across the reply leg and the donated pop with its
settle**: on the state they leave, the endpoint is as it was, the sender a
thread keeping every word the take reads, and the take's in-place guard, read
on the pre-state, still holds.  The pop writes the caller's and the holder's
bindings, the stack's links and the context, never the sender's slot. -/
theorem popDonationSettled_takeGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (scId : SeLe4n.SchedContextId) (home : CoreId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c) (hST : s ≠ tid)
    (hG : receiveTakesInPlace st epId tid s sTcb = true) :
    (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId
        home).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId
          home).objects[s.toObjId]? = some (.tcb sTcb1) ∧
        SenderWordsKept sTcb1 sTcb ∧
        receiveTakesInPlace (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid
          scId home) epId tid s sTcb1 = true := by
  have hSc' : s.toObjId ≠ c.toObjId := fun e => hSC (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hSt' : s.toObjId ≠ tid.toObjId := fun e => hST (SeLe4n.ThreadId.toObjId_injective _ _ e)
  obtain ⟨hE1, sTcb1, hS1, hK, hG1⟩ := storeReplyRendezvous_takeGuard st c tid rid msg ct rp epId
    ep s sTcb hNo hT hFC hRp hE hS hSC hG
  have hNoT := storeReplyRendezvous_noResizeDue st c tid rid msg hNo
  unfold popDonationSettledInPlace
  generalize storeReplyRendezvous st c tid rid msg = T at hE1 hS1 hG1 hNoT
  have hPt := returnDonatedSchedContextInPlace_tcbAt T tid c scId hNoT hSc' hSt' hS1
  have hFr := returnDonatedSchedContextInPlace_popFrame T tid c scId hNoT
  generalize returnDonatedSchedContextInPlace T tid c scId = Rr at hPt hFr
  have hPt' := releaseAgreeAt_of_not_sc (SchedContextOps.settleReturnedContext_agree Rr home scId)
    hPt (fun _ e => by cases e)
  have hF := (settleReturnedContext_popFrame Rr home scId).trans hFr
  obtain ⟨hEP, hGP⟩ := takeGuard_of_popFrame hF hE1 hG1
  exact ⟨hEP, sTcb1, hPt', hK, hGP⟩

/-- **The take's guard across the reply leg and the held pop**: the held pop
writes the holder's binding, the stack's links and the context, never the
sender's slot. -/
theorem keepHeldPop_takeGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (scId : SeLe4n.SchedContextId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c) (hST : s ≠ tid)
    (hG : receiveTakesInPlace st epId tid s sTcb = true) :
    (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
        scId).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
          scId).objects[s.toObjId]? = some (.tcb sTcb1) ∧
        SenderWordsKept sTcb1 sTcb ∧
        receiveTakesInPlace (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg)
          tid scId) epId tid s sTcb1 = true := by
  have hSt' : s.toObjId ≠ tid.toObjId := fun e => hST (SeLe4n.ThreadId.toObjId_injective _ _ e)
  obtain ⟨hE1, sTcb1, hS1, hK, hG1⟩ := storeReplyRendezvous_takeGuard st c tid rid msg ct rp epId
    ep s sTcb hNo hT hFC hRp hE hS hSC hG
  have hNoT := storeReplyRendezvous_noResizeDue st c tid rid msg hNo
  generalize storeReplyRendezvous st c tid rid msg = T at hE1 hS1 hG1 hNoT
  have hPt := keepDonatedSchedContextInPlace_tcbAt T tid scId hNoT hSt' hS1
  obtain ⟨hEP, hGP⟩ := takeGuard_of_popFrame (keepDonatedSchedContextInPlace_popFrame T tid scId hNoT)
    hE1 hG1
  exact ⟨hEP, sTcb1, hPt, hK, hGP⟩

end ReplyLegGuards

end SeLe4n.Kernel
