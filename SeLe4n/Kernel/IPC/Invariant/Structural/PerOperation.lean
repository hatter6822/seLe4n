/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.CallReplyRecv
import SeLe4n.Kernel.IPC.Invariant.NotificationPreservation
import SeLe4n.Kernel.IPC.Invariant.QueueNoDup
import SeLe4n.Kernel.IPC.Invariant.QueueMembership
import SeLe4n.Kernel.IPC.Invariant.QueueNextBlocking
import SeLe4n.Kernel.IPC.Invariant.WaitingThreadHelpers
import SeLe4n.Kernel.IPC.Invariant.Structural.QueueNextTransport
import SeLe4n.Kernel.IPC.Invariant.Structural.StoreObjectFrame
import SeLe4n.Kernel.IPC.Invariant.Structural.DualQueueMembership

/-! # IPC Structural Preservation — Part 4 (PerOperation)

Extracted from `SeLe4n.Kernel.IPC.Invariant.Structural` as part of
AN3-C (IPC-M02 / Theme 4.7) to keep each module under the
2000-LOC maintenance ceiling.  Declarations are unchanged in order,
content, and proof; only the file boundary has moved.  The parent
`Structural.lean` re-exports every child so all existing
`import SeLe4n.Kernel.IPC.Invariant.Structural` consumers continue
to typecheck without modification.

Contains the final per-operation preservation cluster: the M3-E4
WithCaps `dualQueueSystemInvariant` preservation family, the
notification-moved stub comments, and the V3-G / V3-G4 per-operation
preservation witnesses for `endpointSendDual` / `endpointReceiveDual` /
`endpointCall` / `endpointReply`.
-/

-- AN3-C: linter directives inherited from parent Structural.lean.
set_option linter.unusedVariables false

namespace SeLe4n.Kernel

open SeLe4n.Model




-- ============================================================================
-- M3-E4: dualQueueSystemInvariant preservation for WithCaps wrappers
-- ============================================================================

/-- M3-E4: ipcUnwrapCaps preserves dualQueueSystemInvariant.
ipcUnwrapCaps only modifies CNode objects and CDT — endpoint objects, TCB objects
(queue links), and scheduler state are all preserved. The CNode precondition is
established by `lookupCspaceRoot` which verifies receiverRoot is a CNode. -/
theorem ipcUnwrapCaps_preserves_dualQueueSystemInvariant
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (cn : CNode) (hCn : st.objects[receiverRoot]? = some (.cnode cn))
    (hInv : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    dualQueueSystemInvariant st' := by
  -- receiverRoot stays CNode throughout the operation
  have ⟨cn', hCn'⟩ := ipcUnwrapCaps_preserves_cnode_at_root msg senderRoot receiverRoot
    slotBase grantRight st st' summary cn hCn hObjInv hStep
  obtain ⟨hEpWf, hLink, hAcyclic⟩ := hInv
  -- Helper: transfer TCB preservation from st to st' for any oid
  have tcbTransfer : ∀ (oid : SeLe4n.ObjId) (tcb : TCB),
      st.objects[oid]? = some (KernelObject.tcb tcb) →
      st'.objects[oid]? = some (KernelObject.tcb tcb) :=
    fun oid tcb h => ipcUnwrapCaps_preserves_tcb_objects msg senderRoot receiverRoot slotBase
      grantRight st st' summary oid tcb h hObjInv hStep
  -- Helper: transfer object identity from st' to st for non-receiverRoot
  have objBack : ∀ oid, oid ≠ receiverRoot →
      st'.objects[oid]? = st.objects[oid]? :=
    fun oid hNe => ipcUnwrapCaps_preserves_objects_ne msg senderRoot receiverRoot slotBase
      grantRight st st' summary oid hNe hObjInv hStep
  have hLinkFwd := hLink.1
  have hLinkBwd := hLink.2
  refine ⟨?_, ?_, ?_⟩
  -- Part 1: endpoint well-formedness
  · intro epId ep hEpSt'
    -- ep is the same in st (receiverRoot is CNode, can't be endpoint)
    have hEpPre : st.objects[epId]? = some (.endpoint ep) := by
      by_cases hNe : epId = receiverRoot
      · subst hNe; simp [hCn'] at hEpSt'
      · rw [objBack epId hNe] at hEpSt'; exact hEpSt'
    -- dualQueueEndpointWellFormed in st, reduced via hEpPre
    have hWf := hEpWf epId ep hEpPre
    unfold dualQueueEndpointWellFormed at hWf ⊢
    simp only [hEpPre] at hWf; simp only [hEpSt']
    -- hWf : intrusiveQueueWellFormed ep.sendQ st ∧ intrusiveQueueWellFormed ep.receiveQ st
    -- Goal: intrusiveQueueWellFormed ep.sendQ st' ∧ intrusiveQueueWellFormed ep.receiveQ st'
    obtain ⟨⟨hS1, hS2, hS3⟩, ⟨hR1, hR2, hR3⟩⟩ := hWf
    exact ⟨⟨hS1, fun hd hHead => by
        obtain ⟨tcb, hTcb, hPrev⟩ := hS2 hd hHead
        exact ⟨tcb, tcbTransfer _ _ hTcb, hPrev⟩,
      fun tl hTail => by
        obtain ⟨tcb, hTcb, hNext⟩ := hS3 tl hTail
        exact ⟨tcb, tcbTransfer _ _ hTcb, hNext⟩⟩,
    ⟨hR1, fun hd hHead => by
        obtain ⟨tcb, hTcb, hPrev⟩ := hR2 hd hHead
        exact ⟨tcb, tcbTransfer _ _ hTcb, hPrev⟩,
      fun tl hTail => by
        obtain ⟨tcb, hTcb, hNext⟩ := hR3 tl hTail
        exact ⟨tcb, tcbTransfer _ _ hTcb, hNext⟩⟩⟩
  -- Part 2: TCB queue link integrity (forward + backward)
  · constructor
    · intro a tcbA hTcbA' b hNext
      have hTcbAPre : st.objects[a.toObjId]? = some (.tcb tcbA) := by
        by_cases hNe : a.toObjId = receiverRoot
        · subst hNe; simp [hCn'] at hTcbA'
        · rw [objBack _ hNe] at hTcbA'; exact hTcbA'
      obtain ⟨tcbB, hTcbB, hPrev⟩ := hLinkFwd a tcbA hTcbAPre b hNext
      exact ⟨tcbB, tcbTransfer _ _ hTcbB, hPrev⟩
    · intro b tcbB hTcbB' a hPrev
      have hTcbBPre : st.objects[b.toObjId]? = some (.tcb tcbB) := by
        by_cases hNe : b.toObjId = receiverRoot
        · subst hNe; simp [hCn'] at hTcbB'
        · rw [objBack _ hNe] at hTcbB'; exact hTcbB'
      obtain ⟨tcbA, hTcbA, hNext⟩ := hLinkBwd b tcbB hTcbBPre a hPrev
      exact ⟨tcbA, tcbTransfer _ _ hTcbA, hNext⟩
  -- Part 3: TCB queue chain acyclicity (only CNode at receiverRoot changes, not TCBs)
  · have hTransfer : ∀ a b, QueueNextPath st' a b → QueueNextPath st a b := by
      intro a b hp
      induction hp with
      | single x y tcbX hObj hNext =>
        have hObjPre : st.objects[x.toObjId]? = some (.tcb tcbX) := by
          by_cases hNe : x.toObjId = receiverRoot
          · subst hNe; simp [hCn'] at hObj
          · rw [objBack _ hNe] at hObj; exact hObj
        exact .single x y tcbX hObjPre hNext
      | cons x y z tcbX hObj hNext _ ih =>
        have hObjPre : st.objects[x.toObjId]? = some (.tcb tcbX) := by
          by_cases hNe : x.toObjId = receiverRoot
          · subst hNe; simp [hCn'] at hObj
          · rw [objBack _ hNe] at hObj; exact hObj
        exact .cons x y z tcbX hObjPre hNext ih
    intro t hp; exact hAcyclic t (hTransfer t t hp)

/-- M3-E4: endpointSendDualWithCaps preserves dualQueueSystemInvariant.
Composes endpointSendDual base preservation with ipcUnwrapCaps preservation.
The CNode precondition requires that when immediate rendezvous occurs, the
receiver's cspaceRoot points to an actual CNode in the intermediate state. -/
theorem endpointSendDualWithCaps_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : dualQueueSystemInvariant st)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hCnodeRoot : ∀ (stMid : SystemState) (recvRoot : SeLe4n.ObjId),
      endpointSendDual endpointId sender msg st = .ok ((), stMid) →
      ∃ cn, stMid.objects[recvRoot]? = some (.cnode cn))
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
              senderCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    dualQueueSystemInvariant st' := by
  simp only [endpointSendDualWithCaps] at hStep
  cases hSend : endpointSendDual endpointId sender msg st with
  | error e => simp [hSend] at hStep
  | ok pair =>
    rcases pair with ⟨_, stMid⟩
    simp only [hSend] at hStep
    have hInvMid := endpointSendDual_preserves_dualQueueSystemInvariant endpointId sender msg
      st stMid hObjInv hSend hInv hFreshSender hSendTailFresh
    have hObjInvMid : stMid.objects.invExt :=
      endpointSendDual_preserves_objects_invExt st stMid endpointId sender msg hObjInv hSend
    -- All paths either return stMid directly or go through ipcUnwrapCaps
    -- Case-split on the objects to determine hasReceiver before touching hStep
    cases hObj : st.objects[endpointId]? with
    | none =>
      simp [hObj] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
    | some obj =>
      cases obj with
      | endpoint ep =>
        cases hHead : ep.receiveQ.head with
        | none =>
          simp [hObj, hHead] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
        | some receiverId =>
          -- hasReceiver = true, guard = msg.caps.isEmpty
          by_cases hEmpty : msg.caps.isEmpty = true
          · simp [hObj, hHead, hEmpty] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
          · -- Cap transfer path
            simp [hObj, hHead, hEmpty] at hStep
            cases hLookup : lookupCspaceRoot stMid receiverId with
            | none => simp [hLookup] at hStep -- AK1-I: fail-closed, vacuous
            | some recvRoot =>
              simp only [hLookup] at hStep
              obtain ⟨cn, hCn⟩ := hCnodeRoot stMid recvRoot hSend
              exact ipcUnwrapCaps_preserves_dualQueueSystemInvariant msg senderCspaceRoot
                recvRoot receiverSlotBase _ stMid st' summary cn hCn hInvMid hObjInvMid hStep
      | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ =>
        simp [hObj] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid

/-- M3-E4: endpointReceiveDualWithCaps preserves dualQueueSystemInvariant.
Composes endpointReceiveDual base preservation with ipcUnwrapCaps preservation. -/
theorem endpointReceiveDualWithCaps_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (endpointRights : AccessRightSet)
    (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (summary : CapTransferSummary)
    (hInv : dualQueueSystemInvariant st)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hCnodeRoot : ∀ (stMid : SystemState),
      endpointReceiveDual endpointId receiver st = .ok (senderId, stMid) →
      ∃ cn, stMid.objects[receiverCspaceRoot]? = some (.cnode cn))
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDualWithCaps endpointId receiver endpointRights
              receiverCspaceRoot receiverSlotBase st = .ok ((senderId, summary), st')) :
    dualQueueSystemInvariant st' := by
  simp only [endpointReceiveDualWithCaps] at hStep
  cases hRecv : endpointReceiveDual endpointId receiver st with
  | error e => simp [hRecv] at hStep
  | ok pair =>
    rcases pair with ⟨sid, stMid⟩
    simp only [hRecv] at hStep
    have hInvMid := endpointReceiveDual_preserves_dualQueueSystemInvariant endpointId receiver
      st stMid sid hObjInv hRecv hInv hFreshReceiver hRecvTailFresh
    have hObjInvMid : stMid.objects.invExt :=
      endpointReceiveDual_preserves_objects_invExt st stMid endpointId receiver sid hObjInv hRecv
    -- All paths return stMid (invariant holds) or go through ipcUnwrapCaps (compose)
    cases hTcb : stMid.objects[receiver.toObjId]? with
    | none => simp [hTcb] at hStep; obtain ⟨⟨rfl, _⟩, rfl⟩ := hStep; exact hInvMid
    | some obj =>
      simp only [hTcb] at hStep
      cases obj with
      | tcb receiverTcb =>
        cases hMsg : receiverTcb.pendingMessage with
        | none => simp [hMsg] at hStep; obtain ⟨⟨rfl, _⟩, rfl⟩ := hStep; exact hInvMid
        | some msg =>
          simp only [hMsg] at hStep
          by_cases hEmpty : msg.caps.isEmpty
          · simp [hEmpty] at hStep; obtain ⟨⟨rfl, _⟩, rfl⟩ := hStep; exact hInvMid
          · simp [hEmpty] at hStep
            -- U-H13: match on lookupCspaceRoot — none returns error, some proceeds
            cases hLookup : lookupCspaceRoot stMid sid with
            | none =>
              -- Missing CSpace root returns error, contradicting .ok
              simp only [hLookup] at hStep; contradiction
            | some senderRoot =>
              simp only [hLookup] at hStep
              -- ipcUnwrapCaps path
              split at hStep
              · -- ipcUnwrapCaps errored — contradiction with hStep : ... = .ok
                exact absurd hStep (by simp)
              · -- ipcUnwrapCaps succeeded
                rename_i hUnwrapResult
                obtain ⟨⟨rfl, _⟩, rfl⟩ := hStep
                obtain ⟨cn, hCn⟩ := hCnodeRoot stMid hRecv
                exact ipcUnwrapCaps_preserves_dualQueueSystemInvariant msg _ receiverCspaceRoot
                  receiverSlotBase _ stMid _ _ cn hCn hInvMid hObjInvMid hUnwrapResult
      | endpoint _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ =>
        obtain ⟨⟨rfl, _⟩, rfl⟩ := hStep; exact hInvMid

theorem endpointQueueRemoveDual_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink, hAcyclic⟩ := hInv
  unfold endpointQueueRemoveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ => simp at hStep
    | endpoint ep =>
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
        have hNeEpTid : endpointId ≠ tid.toObjId :=
          fun h => by rw [h] at hObj; rw [hTcbObj] at hObj; cases hObj
        have hPreEp : ∀ t : TCB, st.objects[endpointId]? ≠ some (.tcb t) :=
          fun t h => by rw [hObj] at h; cases h
        have hEpWf := hEpInv endpointId ep hObj
        unfold dualQueueEndpointWellFormed at hEpWf; simp only [hObj] at hEpWf
        cases hPPrev : tcb.queuePPrev with
        | none => simp [hPPrev] at hStep
        | some pprev =>
          simp only [hPPrev] at hStep
          -- isNone guard
          generalize hQ : (if isReceiveQ then ep.receiveQ else ep.sendQ) = q at hStep
          split at hStep
          · simp at hStep
          · rename_i hNotIsNone
            -- pprevConsistent guard
            cases pprev with
            | endpointHead =>
              simp only [] at hStep
              split at hStep
              · simp at hStep
              · -- pprevConsistent passed: q.head = some tid ∧ tcb.queuePrev.isNone
                rename_i hConsist
                -- applyPrev: storeObject endpointId ep' st → st1
                cases hStoreEp1 : storeObject endpointId
                    (.endpoint (if isReceiveQ then { ep with receiveQ := { head := tcb.queueNext, tail := q.tail } }
                     else { ep with sendQ := { head := tcb.queueNext, tail := q.tail } })) st with
                | error e => simp [hStoreEp1] at hStep
                | ok pair1 =>
                  simp only [hStoreEp1] at hStep
                  -- Extract guard facts from pprevConsistent
                  have hQHeadTid : q.head = some tid := by simp_all
                  have hPrevNone : tcb.queuePrev = none := by simp_all
                  have hWfQ : intrusiveQueueWellFormed q st := by rw [← hQ]; cases isReceiveQ <;> simp_all
                  obtain ⟨hHT, hHdBnd, hTlBnd⟩ := hWfQ
                  obtain ⟨_, hTcbH, hPrevNone'⟩ := hHdBnd tid hQHeadTid
                  rw [hTcbObj] at hTcbH; cases hTcbH
                  -- Now case-split on tcb.queueNext (Path A vs Path B)
                  cases hNext : tcb.queueNext with
                  | none =>
                    -- PATH A: sole element removal (endpointHead, queueNext=none)
                    simp only [hNext, hQHeadTid] at hStep
                    generalize hStoreEp2 : storeObject endpointId _ pair1.2 = rEp2 at hStep
                    cases rEp2 with
                    | error e => simp at hStep
                    | ok pair3 =>
                      simp only [] at hStep
                      generalize hClear : storeTcbQueueLinks pair3.2 tid none none none = rCl at hStep
                      cases rCl with
                      | error e => simp at hStep
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                        obtain ⟨_, rfl⟩ := hStep
                        have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hObjInv hStoreEp1
                        have hObjInv3 := storeObject_preserves_objects_invExt' pair1.2 endpointId _ pair3 hObjInv1 hStoreEp2
                        have hLink1 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                          st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp hLink
                        have hPreEp2 : ∀ t : TCB, pair1.2.objects[endpointId]? ≠ some (.tcb t) := by
                          intro t h; rw [storeObject_objects_eq st pair1.2 endpointId _ hObjInv hStoreEp1] at h; cases h
                        have hLink2 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                          pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2 hPreEp2 hLink1
                        have hTransport : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                            pair3.2.objects[x.toObjId]? = some (.tcb t) →
                            st.objects[x.toObjId]? = some (.tcb t) := by
                          intro x t h
                          have h1 : pair1.2.objects[x.toObjId]? = some (.tcb t) := by
                            by_cases hx : x.toObjId = endpointId
                            · rw [hx, storeObject_objects_eq pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2] at h; cases h
                            · rwa [storeObject_objects_ne pair1.2 pair3.2 endpointId x.toObjId _ hx hObjInv1 hStoreEp2] at h
                          by_cases hx : x.toObjId = endpointId
                          · rw [hx, storeObject_objects_eq st pair1.2 endpointId _ hObjInv hStoreEp1] at h1; cases h1
                          · rwa [storeObject_objects_ne st pair1.2 endpointId x.toObjId _ hx hObjInv hStoreEp1] at h1
                        have hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
                            pair3.2.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some tid := by
                          intro a tA hA hN
                          obtain ⟨_, hB, hP⟩ := hLink.1 a tA (hTransport a tA hA) tid hN
                          rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                        have hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB),
                            pair3.2.objects[b.toObjId]? = some (.tcb tcbB) → tcbB.queuePrev ≠ some tid := by
                          intro b tB hB hP
                          obtain ⟨_, hA, hN⟩ := hLink.2 b tB (hTransport b tB hB) tid hP
                          rw [hTcbObj] at hA; cases hA; rw [hNext] at hN; exact absurd hN (by simp)
                        -- Acyclicity chain
                        have hAcycEp1 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                          st pair1.2 endpointId _ (fun _ h => by cases h) hObjInv hStoreEp1 hAcyclic
                        have hAcycEp3 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                          pair1.2 pair3.2 endpointId _ (fun _ h => by cases h) hObjInv1 hStoreEp2 hAcycEp1
                        refine ⟨?_, storeTcbQueueLinks_clearing_preserves_linkInteg
                          pair3.2 st4 tid hObjInv3 hClear hLink2 hNoFwd hNoRev,
                          storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                          pair3.2 st4 tid none none hObjInv3 hClear hAcycEp3⟩
                        intro epId' ep' hObj'
                        have hObj1 := storeTcbQueueLinks_endpoint_backward pair3.2 st4 tid none none none
                          epId' ep' hObjInv3 hClear hObj'
                        unfold dualQueueEndpointWellFormed; rw [hObj']
                        by_cases hNe : epId' = endpointId
                        · rw [hNe] at hObj1
                          rw [storeObject_objects_eq pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2] at hObj1
                          cases hObj1
                          cases hRQ : isReceiveQ
                          · exact ⟨intrusiveQueueWellFormed_empty st4,
                              storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClear
                                ep.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2 hPreEp2 _
                                  (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                    st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp _ hEpWf.2))
                                (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
                          · exact ⟨storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClear
                                ep.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2 hPreEp2 _
                                  (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                    st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp _ hEpWf.1))
                                (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                              intrusiveQueueWellFormed_empty st4⟩
                        · have hObjSt1 : pair1.2.objects[epId']? = some (.endpoint ep') := by
                            rwa [storeObject_objects_ne pair1.2 pair3.2 endpointId epId' _ hNe hObjInv1 hStoreEp2] at hObj1
                          have hObjSt : st.objects[epId']? = some (.endpoint ep') := by
                            rwa [storeObject_objects_ne st pair1.2 endpointId epId' _ hNe hObjInv hStoreEp1] at hObjSt1
                          have hWfPre := hEpInv epId' ep' hObjSt
                          unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjSt] at hWfPre
                          exact ⟨storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClear
                              ep'.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2 hPreEp2 _
                                (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp _ hWfPre.1))
                              (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                            storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClear
                              ep'.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                pair1.2 pair3.2 endpointId _ hObjInv1 hStoreEp2 hPreEp2 _
                                (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp _ hWfPre.2))
                              (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
                  | some nextTid =>
                    -- PATH B: head removal with successor (endpointHead, queueNext=some nextTid)
                    simp only [hNext] at hStep
                    -- st2Result: lookupTcb pair1.2 nextTid → storeTcbQueueLinks
                    cases hLkN : lookupTcb pair1.2 nextTid with
                    | none => simp [hLkN] at hStep
                    | some nextTcb =>
                      simp only [hLkN] at hStep
                      generalize hStN : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext = rStN at hStep
                      cases rStN with
                      | error e => simp at hStep
                      | ok st2 =>
                        simp only [hQHeadTid] at hStep
                        generalize hStoreEp2 : storeObject endpointId _ st2 = rEp2 at hStep
                        cases rEp2 with
                        | error e => simp at hStep
                        | ok pair3 =>
                          simp only [] at hStep
                          generalize hClear : storeTcbQueueLinks pair3.2 tid none none none = rCl at hStep
                          cases rCl with
                          | error e => simp at hStep
                          | ok st4 =>
                            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                            obtain ⟨_, rfl⟩ := hStep
                            -- Key intermediate facts
                            have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hObjInv hStoreEp1
                            have hTransport1 : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                pair1.2.objects[x.toObjId]? = some (.tcb t) →
                                st.objects[x.toObjId]? = some (.tcb t) := by
                              intro x t h; by_cases hx : x.toObjId = endpointId
                              · rw [hx, storeObject_objects_eq st pair1.2 endpointId _ hObjInv hStoreEp1] at h; cases h
                              · rwa [storeObject_objects_ne st pair1.2 endpointId x.toObjId _ hx hObjInv hStoreEp1] at h
                            have hNeEpNext : endpointId ≠ nextTid.toObjId := by
                              intro h; have := lookupTcb_some_objects pair1.2 nextTid nextTcb hLkN
                              rw [← h, storeObject_objects_eq st pair1.2 endpointId _ hObjInv hStoreEp1] at this; cases this
                            have hNextTcbSt : st.objects[nextTid.toObjId]? = some (.tcb nextTcb) :=
                              hTransport1 nextTid nextTcb (lookupTcb_some_objects pair1.2 nextTid nextTcb hLkN)
                            have hNextPrevB : nextTcb.queuePrev = some tid := by
                              obtain ⟨_, hB, hP⟩ := hLink.1 tid tcb hTcbObj nextTid hNext
                              rw [hNextTcbSt] at hB; cases hB; exact hP
                            have hNeHN : tid.toObjId ≠ nextTid.toObjId := by
                              intro h; have hEq : st.objects[nextTid.toObjId]? = some (.tcb tcb) := h ▸ hTcbObj
                              rw [hNextTcbSt] at hEq; cases hEq; rw [hPrevNone] at hNextPrevB; exact absurd hNextPrevB (by simp)
                            have hLink1 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                              st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp hLink
                            have hObjInvSt2 := storeTcbQueueLinks_preserves_objects_invExt
                              pair1.2 st2 nextTid _ _ _ hObjInv1 hStN
                            have hPreEp2 : ∀ t : TCB, st2.objects[endpointId]? ≠ some (.tcb t) := by
                              intro t h
                              rw [storeTcbQueueLinks_preserves_objects_ne pair1.2 st2 nextTid _ _ _
                                endpointId hNeEpNext hObjInv1 hStN,
                                storeObject_objects_eq st pair1.2 endpointId _ hObjInv hStoreEp1] at h; cases h
                            have hObjInv3 := storeObject_preserves_objects_invExt' st2 endpointId _ pair3 hObjInvSt2 hStoreEp2
                            -- nextTid result in st2
                            have hNextResultB := storeTcbQueueLinks_result_tcb pair1.2 st2 nextTid _ _ _ hObjInv1 hStN
                            obtain ⟨origNextB, hOrigLkB, hNextSt2B⟩ := hNextResultB
                            rw [hLkN] at hOrigLkB; cases hOrigLkB
                            rw [hPrevNone] at hNextSt2B
                            -- nextTid in pair3.2 (preserved through storeObject)
                            have hNS3 : pair3.2.objects[nextTid.toObjId]? = some
                                (.tcb (tcbWithQueueLinks nextTcb none (some QueuePPrev.endpointHead) nextTcb.queueNext)) := by
                              rw [storeObject_objects_ne st2 pair3.2 endpointId nextTid.toObjId _
                                (Ne.symm hNeEpNext) hObjInvSt2 hStoreEp2]; exact hNextSt2B
                            -- hNoFwd/hNoRev for clearing step
                            have hTransport3 : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                pair3.2.objects[x.toObjId]? = some (.tcb t) →
                                x.toObjId ≠ nextTid.toObjId →
                                st.objects[x.toObjId]? = some (.tcb t) := by
                              intro x t h hxN
                              have h2 : st2.objects[x.toObjId]? = some (.tcb t) := by
                                by_cases hx : x.toObjId = endpointId
                                · rw [hx, storeObject_objects_eq st2 pair3.2 endpointId _ hObjInvSt2 hStoreEp2] at h; cases h
                                · rwa [storeObject_objects_ne st2 pair3.2 endpointId x.toObjId _ hx hObjInvSt2 hStoreEp2] at h
                              have h1 : pair1.2.objects[x.toObjId]? = some (.tcb t) := by
                                rwa [storeTcbQueueLinks_preserves_objects_ne pair1.2 st2 nextTid _ _ _
                                  x.toObjId hxN hObjInv1 hStN] at h2
                              exact hTransport1 x t h1
                            have hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
                                pair3.2.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some tid := by
                              intro a tA hA hN
                              by_cases haN : a.toObjId = nextTid.toObjId
                              · have hNS3' := hNS3; rw [haN] at hA; rw [hNS3'] at hA; cases hA
                                simp [tcbWithQueueLinks] at hN
                                obtain ⟨_, hB, hP⟩ := hLink.1 nextTid nextTcb hNextTcbSt tid hN
                                rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                              · have hA' := hTransport3 a tA hA haN
                                obtain ⟨_, hB, hP⟩ := hLink.1 a tA hA' tid hN
                                rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                            have hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB),
                                pair3.2.objects[b.toObjId]? = some (.tcb tcbB) → tcbB.queuePrev ≠ some tid := by
                              intro b tB hB hP
                              by_cases hbN : b.toObjId = nextTid.toObjId
                              · rw [hbN] at hB; rw [hNS3] at hB; cases hB; simp [tcbWithQueueLinks] at hP
                              · have hB' := hTransport3 b tB hB hbN
                                obtain ⟨_, hA, hN⟩ := hLink.2 b tB hB' tid hP
                                rw [hTcbObj] at hA; cases hA; rw [hNext] at hN
                                exact absurd (congrArg ThreadId.toObjId (Option.some.inj hN).symm) hbN
                            -- TCB snapshots in st4
                            have hTidResult := storeTcbQueueLinks_result_tcb pair3.2 st4 tid none none none hObjInv3 hClear
                            obtain ⟨_, _, hTidSt4⟩ := hTidResult
                            have hObjInv4 := storeTcbQueueLinks_preserves_objects_invExt pair3.2 st4 tid none none none hObjInv3 hClear
                            have hNextSt4 : st4.objects[nextTid.toObjId]? = some
                                (.tcb (tcbWithQueueLinks nextTcb none (some QueuePPrev.endpointHead) nextTcb.queueNext)) := by
                              rw [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid none none none
                                nextTid.toObjId hNeHN.symm hObjInv3 hClear]; exact hNS3
                            -- Other TCBs in st4 = other TCBs in st
                            have hFwdOther : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                x.toObjId ≠ tid.toObjId → x.toObjId ≠ nextTid.toObjId →
                                st.objects[x.toObjId]? = some (.tcb t) →
                                st4.objects[x.toObjId]? = some (.tcb t) := by
                              intro x t hxT hxN ht
                              rw [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid _ _ _
                                x.toObjId hxT hObjInv3 hClear,
                                storeObject_objects_ne st2 pair3.2 endpointId x.toObjId _ ?_ hObjInvSt2 hStoreEp2,
                                storeTcbQueueLinks_preserves_objects_ne pair1.2 st2 nextTid _ _ _
                                x.toObjId hxN hObjInv1 hStN,
                                storeObject_objects_ne st pair1.2 endpointId x.toObjId _ ?_ hObjInv hStoreEp1]; exact ht
                              · intro h; rw [h] at ht; rw [hObj] at ht; cases ht
                              · intro h; rw [h] at ht; rw [hObj] at ht; cases ht
                            have hBackOther : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                x.toObjId ≠ tid.toObjId → x.toObjId ≠ nextTid.toObjId →
                                st4.objects[x.toObjId]? = some (.tcb t) →
                                st.objects[x.toObjId]? = some (.tcb t) := by
                              intro x t hxT hxN ht
                              have h3 : pair3.2.objects[x.toObjId]? = some (.tcb t) := by
                                rwa [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid _ _ _
                                  x.toObjId hxT hObjInv3 hClear] at ht
                              exact hTransport3 x t h3 hxN
                            -- iqwf transport helper
                            have hNextTailProp : ∀ (qq : IntrusiveQueue),
                                intrusiveQueueWellFormed qq st →
                                ∀ tl, qq.tail = some tl → tl.toObjId = nextTid.toObjId →
                                nextTcb.queueNext = none := by
                              intro qq hWfQQ tl hTl hEq
                              have hTlEq := threadId_toObjId_injective hEq; rw [hTlEq] at hTl
                              obtain ⟨_, hT, hN⟩ := hWfQQ.2.2 nextTid hTl
                              rw [hNextTcbSt] at hT; cases hT; exact hN
                            have hIqwfTransport : ∀ (qq : IntrusiveQueue),
                                intrusiveQueueWellFormed qq st →
                                intrusiveQueueWellFormed qq st4 := by
                              intro qq hWfQQ
                              exact storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClear qq
                                (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st2 pair3.2 endpointId _ hObjInvSt2 hStoreEp2 hPreEp2 qq
                                  (storeTcbQueueLinks_preserves_iqwf pair1.2 st2 nextTid _ _ _ hObjInv1 hStN qq
                                    (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                      st pair1.2 endpointId _ hObjInv hStoreEp1 hPreEp qq hWfQQ)
                                    (fun _ _ _ => hPrevNone) (hNextTailProp qq hWfQQ)))
                                (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                            -- Acyclicity chain
                            have hAcycEp1 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                              st pair1.2 endpointId _ (fun _ h => by cases h) hObjInv hStoreEp1 hAcyclic
                            have hAcycSt2 := storeTcbQueueLinks_preserveNext_preserves_tcbQueueChainAcyclic
                              pair1.2 st2 nextTid _ _ nextTcb.queueNext hObjInv1 hStN
                              (fun tcb' h => by rw [hLkN] at h; cases h; rfl) hAcycEp1
                            have hAcycEp3 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                              st2 pair3.2 endpointId _ (fun _ h => by cases h) hObjInvSt2 hStoreEp2 hAcycSt2
                            have hAcycSt4 := storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                              pair3.2 st4 tid none none hObjInv3 hClear hAcycEp3
                            -- SPLIT
                            refine ⟨?_, ?_, hAcycSt4⟩
                            -- PART 1: Endpoint well-formedness
                            · intro epId' ep' hObj'
                              have hObj4 := storeTcbQueueLinks_endpoint_backward pair3.2 st4 tid none none none
                                epId' ep' hObjInv3 hClear hObj'
                              unfold dualQueueEndpointWellFormed; rw [hObj']
                              by_cases hNe : epId' = endpointId
                              · rw [hNe] at hObj4
                                rw [storeObject_objects_eq st2 pair3.2 endpointId _ hObjInvSt2 hStoreEp2] at hObj4; cases hObj4
                                have hWfNew : intrusiveQueueWellFormed
                                    { head := some nextTid, tail := q.tail } st4 := by
                                  refine ⟨⟨fun h => absurd h (by simp), fun h => absurd (hHT.2 h) (by rw [hQHeadTid]; simp)⟩, ?_, ?_⟩
                                  · intro hd hHdEq; cases hHdEq
                                    exact ⟨_, hNextSt4, by simp [tcbWithQueueLinks]⟩
                                  · intro tl hTl
                                    obtain ⟨tOrig, hTOrig, hTNextOrig⟩ := hTlBnd tl hTl
                                    by_cases htT : tl.toObjId = tid.toObjId
                                    · have := threadId_toObjId_injective htT; subst this
                                      rw [hTcbObj] at hTOrig; cases hTOrig
                                      rw [hNext] at hTNextOrig; exact absurd hTNextOrig (by simp)
                                    · by_cases htN : tl.toObjId = nextTid.toObjId
                                      · have := threadId_toObjId_injective htN; subst this
                                        rw [hNextTcbSt] at hTOrig; cases hTOrig
                                        exact ⟨_, hNextSt4, by simp [tcbWithQueueLinks]; exact hTNextOrig⟩
                                      · exact ⟨tOrig, hFwdOther tl tOrig htT htN hTOrig, hTNextOrig⟩
                                cases hRQ : isReceiveQ
                                · simp only [Bool.false_eq_true, ↓reduceIte] at hWfNew ⊢
                                  exact ⟨hWfNew, hIqwfTransport ep.receiveQ hEpWf.2⟩
                                · simp only [↓reduceIte] at hWfNew ⊢
                                  exact ⟨hIqwfTransport ep.sendQ hEpWf.1, hWfNew⟩
                              · have hObj4St2 : st2.objects[epId']? = some (.endpoint ep') := by
                                  rwa [storeObject_objects_ne st2 pair3.2 endpointId epId' _ hNe hObjInvSt2 hStoreEp2] at hObj4
                                have hObjPB := storeTcbQueueLinks_endpoint_backward pair1.2 st2 nextTid _ _ _
                                  epId' ep' hObjInv1 hStN hObj4St2
                                have hObjStOrig : st.objects[epId']? = some (.endpoint ep') := by
                                  rwa [storeObject_objects_ne st pair1.2 endpointId epId' _ hNe hObjInv hStoreEp1] at hObjPB
                                have hWfPre := hEpInv epId' ep' hObjStOrig
                                unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjStOrig] at hWfPre
                                exact ⟨hIqwfTransport ep'.sendQ hWfPre.1, hIqwfTransport ep'.receiveQ hWfPre.2⟩
                            -- PART 2: Link integrity
                            · constructor
                              · intro a tcbA hA b hNxt
                                by_cases haT : a.toObjId = tid.toObjId
                                · rw [haT] at hA; rw [hTidSt4] at hA; cases hA; simp [tcbWithQueueLinks] at hNxt
                                · by_cases haN : a.toObjId = nextTid.toObjId
                                  · rw [haN] at hA; rw [hNextSt4] at hA; cases hA
                                    simp [tcbWithQueueLinks] at hNxt
                                    obtain ⟨tcbB, hB, hP⟩ := hLink.1 nextTid nextTcb hNextTcbSt b hNxt
                                    have hbT : b.toObjId ≠ tid.toObjId := by
                                      intro hh; have := threadId_toObjId_injective hh; subst this
                                      rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                                    have hbN : b.toObjId ≠ nextTid.toObjId := by
                                      intro hh; have hbEq := threadId_toObjId_injective hh
                                      rw [hbEq, hNextTcbSt] at hB; cases hB; rw [hNextPrevB] at hP
                                      exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP)) hNeHN
                                    exact ⟨tcbB, hFwdOther b tcbB hbT hbN hB, (threadId_toObjId_injective haN) ▸ hP⟩
                                  · have hA' := hBackOther a tcbA haT haN hA
                                    obtain ⟨tcbB, hB, hP⟩ := hLink.1 a tcbA hA' b hNxt
                                    have hbT : b.toObjId ≠ tid.toObjId := by
                                      intro hh; have := threadId_toObjId_injective hh; subst this
                                      rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                                    have hbN : b.toObjId ≠ nextTid.toObjId := by
                                      intro hh; have hbEq := threadId_toObjId_injective hh
                                      rw [hbEq, hNextTcbSt] at hB; cases hB; rw [hNextPrevB] at hP
                                      exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP).symm) haT
                                    exact ⟨tcbB, hFwdOther b tcbB hbT hbN hB, hP⟩
                              · intro b tcbB hB a hPrv
                                by_cases hbT : b.toObjId = tid.toObjId
                                · rw [hbT] at hB; rw [hTidSt4] at hB; cases hB; simp [tcbWithQueueLinks] at hPrv
                                · by_cases hbN : b.toObjId = nextTid.toObjId
                                  · rw [hbN] at hB; rw [hNextSt4] at hB; cases hB
                                    simp [tcbWithQueueLinks] at hPrv
                                  · have hB' := hBackOther b tcbB hbT hbN hB
                                    obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 b tcbB hB' a hPrv
                                    by_cases haT : a.toObjId = tid.toObjId
                                    · have haEq := threadId_toObjId_injective haT
                                      rw [haEq, hTcbObj] at hA; cases hA; rw [hNext] at hNxt
                                      exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt).symm) hbN
                                    · by_cases haN : a.toObjId = nextTid.toObjId
                                      · have := threadId_toObjId_injective haN; subst this
                                        rw [hNextTcbSt] at hA; cases hA
                                        exact ⟨_, hNextSt4, by simp [tcbWithQueueLinks]; exact hNxt⟩
                                      · exact ⟨tcbA, hFwdOther a tcbA haT haN hA, hNxt⟩
            | tcbNext prevTid =>
              dsimp only at hStep
              split at hStep
              · simp at hStep
              · -- pprevConsistent for tcbNext: q.head ≠ some tid ∧ tcb.queuePrev = some prevTid
                have hQHeadNeTid : q.head ≠ some tid := by simp_all
                have hPrevSome : tcb.queuePrev = some prevTid := by simp_all
                have hWfQ : intrusiveQueueWellFormed q st := by rw [← hQ]; cases isReceiveQ <;> simp_all
                obtain ⟨hHT, hHdBnd, hTlBnd⟩ := hWfQ
                -- applyPrev: lookupTcb st prevTid → prevTcb → storeTcbQueueLinks
                cases hLookupP : lookupTcb st prevTid with
                | none => simp [hLookupP] at hStep
                | some prevTcb =>
                  simp only [hLookupP] at hStep
                  -- Guard: prevTcb.queueNext = some tid
                  split at hStep
                  · simp at hStep
                  · rename_i stAp heqAp
                    split at heqAp
                    · simp at heqAp
                    · cases hLinkP : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcb.queueNext with
                      | error e => simp [hLinkP] at heqAp
                      | ok stPrev =>
                        simp [hLinkP] at heqAp; subst heqAp
                        have hPrevTcbObj := lookupTcb_some_objects st prevTid prevTcb hLookupP
                        have hPrevNextTid : prevTcb.queueNext = some tid := by
                          rename_i hGuard _ _; revert hGuard; simp_all
                        have hNeEpPrev : endpointId ≠ prevTid.toObjId :=
                          fun h => by rw [h] at hObj; rw [hPrevTcbObj] at hObj; cases hObj
                        have hObjInv1 := storeTcbQueueLinks_preserves_objects_invExt
                          st stPrev prevTid _ _ _ hObjInv hLinkP
                        cases hNext : tcb.queueNext with
                        | none =>
                          -- PATH C: tail removal (tcbNext, queueNext=none)
                          simp only [hNext] at hStep
                          generalize hStoreEpC : storeObject endpointId _ stPrev = rEpC at hStep
                          cases rEpC with
                          | error e => simp at hStep
                          | ok pair3 =>
                            simp only [] at hStep
                            generalize hClearC : storeTcbQueueLinks pair3.2 tid none none none = rClC at hStep
                            cases rClC with
                            | error e => simp at hStep
                            | ok st4 =>
                              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                              obtain ⟨_, rfl⟩ := hStep
                              -- Key facts
                              have hNePrevTid : prevTid.toObjId ≠ tid.toObjId := by
                                intro h
                                have hEq : st.objects[tid.toObjId]? = some (.tcb prevTcb) := h ▸ hPrevTcbObj
                                rw [hTcbObj] at hEq; cases hEq
                                rw [hPrevNextTid] at hNext; exact absurd hNext (by simp)
                              have hPreEpSt1 : ∀ t : TCB, stPrev.objects[endpointId]? ≠ some (.tcb t) := by
                                intro t h
                                rw [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _
                                  endpointId hNeEpPrev hObjInv hLinkP] at h; exact absurd h (hPreEp t)
                              have hObjInv3 := storeObject_preserves_objects_invExt' stPrev endpointId _ pair3 hObjInv1 hStoreEpC
                              -- prevTid result
                              have hPrevResult := storeTcbQueueLinks_result_tcb st stPrev prevTid _ _ _ hObjInv hLinkP
                              obtain ⟨origPrev, hOrigPrevLk, hPrevStPrev⟩ := hPrevResult
                              rw [hLookupP] at hOrigPrevLk; cases hOrigPrevLk
                              rw [hNext] at hPrevStPrev
                              -- prevTid in pair3.2
                              have hPrevSt3 : pair3.2.objects[prevTid.toObjId]? = some
                                  (.tcb (tcbWithQueueLinks prevTcb prevTcb.queuePrev prevTcb.queuePPrev none)) := by
                                rw [storeObject_objects_ne stPrev pair3.2 endpointId prevTid.toObjId _
                                  hNeEpPrev.symm hObjInv1 hStoreEpC]; exact hPrevStPrev
                              -- prevTid in st4
                              have hPrevSt4 : st4.objects[prevTid.toObjId]? = some
                                  (.tcb (tcbWithQueueLinks prevTcb prevTcb.queuePrev prevTcb.queuePPrev none)) := by
                                rw [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid _ _ _
                                  prevTid.toObjId hNePrevTid hObjInv3 hClearC]; exact hPrevSt3
                              -- tid cleared
                              have hTidResult := storeTcbQueueLinks_result_tcb pair3.2 st4 tid none none none hObjInv3 hClearC
                              obtain ⟨_, _, hTidSt4⟩ := hTidResult
                              -- Transport: other TCBs in st4 = other TCBs in st
                              have hTransportC : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                  x.toObjId ≠ tid.toObjId → x.toObjId ≠ prevTid.toObjId →
                                  st.objects[x.toObjId]? = some (.tcb t) →
                                  st4.objects[x.toObjId]? = some (.tcb t) := by
                                intro x t hxT hxP ht
                                rw [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid _ _ _ x.toObjId hxT hObjInv3 hClearC,
                                    storeObject_objects_ne stPrev pair3.2 endpointId x.toObjId _ ?_ hObjInv1 hStoreEpC,
                                    storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP]
                                exact ht
                                intro h; rw [h] at ht; rw [hObj] at ht; cases ht
                              have hBackTransportC : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                  x.toObjId ≠ tid.toObjId → x.toObjId ≠ prevTid.toObjId →
                                  st4.objects[x.toObjId]? = some (.tcb t) →
                                  st.objects[x.toObjId]? = some (.tcb t) := by
                                intro x t hxT hxP ht
                                have h3 : pair3.2.objects[x.toObjId]? = some (.tcb t) := by
                                  rwa [storeTcbQueueLinks_preserves_objects_ne pair3.2 st4 tid _ _ _ x.toObjId hxT hObjInv3 hClearC] at ht
                                have h1 : stPrev.objects[x.toObjId]? = some (.tcb t) := by
                                  by_cases hx : x.toObjId = endpointId
                                  · rw [hx, storeObject_objects_eq stPrev pair3.2 endpointId _ hObjInv1 hStoreEpC] at h3; cases h3
                                  · rwa [storeObject_objects_ne stPrev pair3.2 endpointId x.toObjId _ hx hObjInv1 hStoreEpC] at h3
                                rwa [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP] at h1
                              -- iqwf transport
                              have hIqwfTransportC : ∀ (qq : IntrusiveQueue),
                                  intrusiveQueueWellFormed qq st →
                                  intrusiveQueueWellFormed qq st4 := by
                                intro qq hWfQQ
                                exact storeTcbQueueLinks_preserves_iqwf pair3.2 st4 tid none none none hObjInv3 hClearC qq
                                  (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                    stPrev pair3.2 endpointId _ hObjInv1 hStoreEpC hPreEpSt1 qq
                                    (storeTcbQueueLinks_preserves_iqwf st stPrev prevTid _ _ _ hObjInv hLinkP qq hWfQQ
                                      (fun hd hhd heq => by
                                        have hEq := threadId_toObjId_injective heq
                                        rw [hEq] at hhd
                                        obtain ⟨_, hT, hP⟩ := hWfQQ.2.1 prevTid hhd
                                        rw [hPrevTcbObj] at hT
                                        have := KernelObject.tcb.inj (Option.some.inj hT)
                                        rw [this]; exact hP)
                                      (fun _ _ _ => hNext)))
                                  (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                              -- Acyclicity chain
                              have hLinkPNone : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev none = .ok stPrev := by
                                rw [hNext] at hLinkP; exact hLinkP
                              have hAcycSt1 := storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                                st stPrev prevTid prevTcb.queuePrev prevTcb.queuePPrev hObjInv hLinkPNone hAcyclic
                              have hAcycEp3 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                                stPrev pair3.2 endpointId _ (fun _ h => by cases h) hObjInv1 hStoreEpC hAcycSt1
                              have hAcycSt4 := storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                                pair3.2 st4 tid none none hObjInv3 hClearC hAcycEp3
                              -- Build link integrity for st4 directly
                              have hLinkSt4 : tcbQueueLinkIntegrity st4 := by
                                constructor
                                · intro a tcbA hA b hNxt
                                  by_cases haT : a.toObjId = tid.toObjId
                                  · rw [haT] at hA; rw [hTidSt4] at hA; cases hA; simp [tcbWithQueueLinks] at hNxt
                                  · by_cases haP : a.toObjId = prevTid.toObjId
                                    · rw [haP] at hA; rw [hPrevSt4] at hA; cases hA
                                      simp [tcbWithQueueLinks] at hNxt -- prevTid.next = none
                                    · have hA' := hBackTransportC a tcbA haT haP hA
                                      obtain ⟨tcbB, hB, hP⟩ := hLink.1 a tcbA hA' b hNxt
                                      by_cases hbT : b.toObjId = tid.toObjId
                                      · have hB2 : st.objects[tid.toObjId]? = some (.tcb tcbB) := hbT ▸ hB
                                        rw [hTcbObj] at hB2
                                        have := (KernelObject.tcb.inj (Option.some.inj hB2))
                                        rw [← this, hPrevSome] at hP
                                        exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP).symm) haP
                                      · by_cases hbPP : b.toObjId = prevTid.toObjId
                                        · -- b = prevTid: return prevTid's modified TCB from st4
                                          -- tcbB = prevTcb, so hP : prevTcb.queuePrev = some a
                                          have hBSt4 : st4.objects[b.toObjId]? = some
                                              (.tcb (tcbWithQueueLinks prevTcb prevTcb.queuePrev prevTcb.queuePPrev none)) := by
                                            rw [hbPP]; exact hPrevSt4
                                          -- prevTcb = tcbB
                                          have hTcbBEq : prevTcb = tcbB := by
                                            have h := hbPP ▸ hB; rw [hPrevTcbObj] at h
                                            exact KernelObject.tcb.inj (Option.some.inj h)
                                          exact ⟨_, hBSt4, by simp [tcbWithQueueLinks]; rw [hTcbBEq]; exact hP⟩
                                        · exact ⟨tcbB, hTransportC b tcbB hbT hbPP hB, hP⟩
                                · intro b tcbB hB a hPrv
                                  by_cases hbT : b.toObjId = tid.toObjId
                                  · rw [hbT] at hB; rw [hTidSt4] at hB; cases hB; simp [tcbWithQueueLinks] at hPrv
                                  · by_cases hbP : b.toObjId = prevTid.toObjId
                                    · -- b is prevTid: extract tcbB = tcbWithQueueLinks prevTcb ... via transport
                                      have hB2 : st4.objects[prevTid.toObjId]? = some (.tcb tcbB) := by rw [← hbP]; exact hB
                                      rw [hPrevSt4] at hB2
                                      have hTcbBEq : tcbB = tcbWithQueueLinks prevTcb prevTcb.queuePrev prevTcb.queuePPrev none :=
                                        (KernelObject.tcb.inj (Option.some.inj hB2)).symm
                                      rw [hTcbBEq] at hPrv; simp [tcbWithQueueLinks] at hPrv
                                      -- hPrv : prevTcb.queuePrev = some a
                                      obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 prevTid prevTcb hPrevTcbObj a hPrv
                                      have haT : a.toObjId ≠ tid.toObjId := by
                                        intro hh
                                        have hA2 : st.objects[tid.toObjId]? = some (.tcb tcbA) := hh ▸ hA
                                        rw [hTcbObj] at hA2
                                        have := KernelObject.tcb.inj (Option.some.inj hA2)
                                        rw [← this, hNext] at hNxt; exact absurd hNxt (by simp)
                                      have haP : a.toObjId ≠ prevTid.toObjId := by
                                        intro hh
                                        have hA2 : st.objects[prevTid.toObjId]? = some (.tcb tcbA) := hh ▸ hA
                                        rw [hPrevTcbObj] at hA2
                                        have := KernelObject.tcb.inj (Option.some.inj hA2)
                                        rw [← this, hPrevNextTid] at hNxt
                                        exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt)) hNePrevTid.symm
                                      exact ⟨tcbA, hTransportC a tcbA haT haP hA,
                                        hNxt.trans (congrArg some (threadId_toObjId_injective hbP).symm)⟩
                                    · have hB' := hBackTransportC b tcbB hbT hbP hB
                                      obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 b tcbB hB' a hPrv
                                      by_cases haT : a.toObjId = tid.toObjId
                                      · have hA2 : st.objects[tid.toObjId]? = some (.tcb tcbA) := haT ▸ hA
                                        rw [hTcbObj] at hA2
                                        have := (KernelObject.tcb.inj (Option.some.inj hA2))
                                        rw [← this, hNext] at hNxt
                                        exact absurd hNxt (by simp)
                                      · by_cases haP : a.toObjId = prevTid.toObjId
                                        · have hA2 : st.objects[prevTid.toObjId]? = some (.tcb tcbA) := haP ▸ hA
                                          rw [hPrevTcbObj] at hA2
                                          have hTcbEq := (KernelObject.tcb.inj (Option.some.inj hA2))
                                          -- hTcbEq : prevTcb = tcbA, hNxt : tcbA.queueNext = some b
                                          rw [← hTcbEq, hPrevNextTid] at hNxt
                                          -- hNxt : some tid = some b → tid = b → contradiction with hbT
                                          have := congrArg ThreadId.toObjId (Option.some.inj hNxt)
                                          exact absurd this.symm hbT
                                        · exact ⟨tcbA, hTransportC a tcbA haT haP hA, hNxt⟩
                              -- SPLIT
                              refine ⟨?_, hLinkSt4, hAcycSt4⟩
                              -- PART 1: Endpoint well-formedness
                              intro epId' ep' hObj'
                              have hObj4 := storeTcbQueueLinks_endpoint_backward pair3.2 st4 tid none none none
                                epId' ep' hObjInv3 hClearC hObj'
                              unfold dualQueueEndpointWellFormed; rw [hObj']
                              by_cases hNe : epId' = endpointId
                              · rw [hNe] at hObj4
                                rw [storeObject_objects_eq stPrev pair3.2 endpointId _ hObjInv1 hStoreEpC] at hObj4; cases hObj4
                                -- Modified queue has tail = some prevTid
                                -- Need WF for {head=q.head, tail=some prevTid} in st4
                                have hQHeadSome : q.head ≠ none := by
                                  intro h; simp [h, Option.isNone] at hNotIsNone
                                have hWfNew : intrusiveQueueWellFormed { head := q.head, tail := some prevTid } st4 := by
                                  refine ⟨⟨fun h => absurd h hQHeadSome,
                                          fun h => absurd h (by simp)⟩, ?_, ?_⟩
                                  · intro hd hHdEq
                                    obtain ⟨tHd, hTHd, hPHd⟩ := hHdBnd hd hHdEq
                                    by_cases hdT : hd.toObjId = tid.toObjId
                                    · exact absurd hHdEq (by rw [threadId_toObjId_injective hdT]; exact hQHeadNeTid)
                                    · by_cases hdP : hd.toObjId = prevTid.toObjId
                                      · have := threadId_toObjId_injective hdP; subst this
                                        exact ⟨_, hPrevSt4, by simp [tcbWithQueueLinks]; rw [hPrevTcbObj] at hTHd; cases hTHd; exact hPHd⟩
                                      · exact ⟨tHd, hTransportC hd tHd hdT hdP hTHd, hPHd⟩
                                  · intro tl hTl; cases hTl
                                    exact ⟨_, hPrevSt4, by simp [tcbWithQueueLinks]⟩
                                have hIfSimp : (if q.head = some tid then { head := none, tail := some prevTid : IntrusiveQueue }
                                    else { head := q.head, tail := some prevTid }) =
                                    { head := q.head, tail := some prevTid } := by
                                  simp [hQHeadNeTid]
                                cases hRQ : isReceiveQ
                                · simp only [hIfSimp] at hWfNew ⊢
                                  exact ⟨hWfNew, hIqwfTransportC ep.receiveQ hEpWf.2⟩
                                · simp only [hIfSimp] at hWfNew ⊢
                                  exact ⟨hIqwfTransportC ep.sendQ hEpWf.1, hWfNew⟩
                              · have hObj4St1 : stPrev.objects[epId']? = some (.endpoint ep') := by
                                  rwa [storeObject_objects_ne stPrev pair3.2 endpointId epId' _ hNe hObjInv1 hStoreEpC] at hObj4
                                have hObjStOrig : st.objects[epId']? = some (.endpoint ep') :=
                                  storeTcbQueueLinks_endpoint_backward st stPrev prevTid _ _ _ epId' ep' hObjInv hLinkP hObj4St1
                                have hWfPre := hEpInv epId' ep' hObjStOrig
                                unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjStOrig] at hWfPre
                                exact ⟨hIqwfTransportC ep'.sendQ hWfPre.1, hIqwfTransportC ep'.receiveQ hWfPre.2⟩
                        | some nextTid =>
                          -- PATH D: mid-queue removal (tcbNext, queueNext=some nextTid)
                          simp only [hNext] at hStep
                          -- st2Result: lookupTcb stPrev nextTid → storeTcbQueueLinks
                          cases hLkN : lookupTcb stPrev nextTid with
                          | none => simp [hLkN] at hStep
                          | some nextTcb =>
                            simp only [hLkN] at hStep
                            generalize hStN : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext = rStN at hStep
                            cases rStN with
                            | error e => simp at hStep
                            | ok stNext =>
                              simp only [] at hStep
                              -- q' = {head = q.head, tail = q.tail} since q.head ≠ some tid
                              simp only [hQHeadNeTid, ↓reduceIte] at hStep
                              -- storeObject endpointId ep' stNext → pair4
                              generalize hStoreEpD : storeObject endpointId _ stNext = rEpD at hStep
                              cases rEpD with
                              | error e => simp at hStep
                              | ok pair4 =>
                                simp only [] at hStep
                                generalize hClearD : storeTcbQueueLinks pair4.2 tid none none none = rClD at hStep
                                cases rClD with
                                | error e => simp at hStep
                                | ok stF =>
                                  simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                                  obtain ⟨_, rfl⟩ := hStep
                                  -- === PATH D KEY FACTS ===
                                  have hNePrevTid : prevTid.toObjId ≠ tid.toObjId := by
                                    intro h; apply hAcyclic prevTid
                                    have hPEq := threadId_toObjId_injective h
                                    exact .single prevTid prevTid prevTcb hPrevTcbObj (hPEq ▸ hPrevNextTid)
                                  -- prevTid ≠ nextTid from acyclicity
                                  have hNePrevNext : prevTid.toObjId ≠ nextTid.toObjId := by
                                    intro h
                                    have hEq : nextTid = prevTid := (threadId_toObjId_injective h).symm
                                    apply hAcyclic tid
                                    have hObj1 : st.objects[nextTid.toObjId]? = some (.tcb prevTcb) := by
                                      rw [← h]; exact hPrevTcbObj
                                    exact .cons tid nextTid tid tcb hTcbObj hNext
                                      (.single nextTid tid prevTcb hObj1 hPrevNextTid)
                                  have hNextTcbSt : st.objects[nextTid.toObjId]? = some (.tcb nextTcb) := by
                                    have hN1 := lookupTcb_some_objects stPrev nextTid nextTcb hLkN
                                    rwa [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _
                                      nextTid.toObjId hNePrevNext.symm hObjInv hLinkP] at hN1
                                  have hNeEpNext : endpointId ≠ nextTid.toObjId := by
                                    intro h; rw [h] at hObj; rw [hNextTcbSt] at hObj; cases hObj
                                  have hNeNextTid : nextTid.toObjId ≠ tid.toObjId := by
                                    intro h
                                    -- nextTid = tid creates a self-loop
                                    have hEq := threadId_toObjId_injective h
                                    apply hAcyclic tid
                                    exact .single tid tid tcb hTcbObj (hEq ▸ hNext)
                                  -- nextTcb.queuePrev = some tid (from link integrity)
                                  have hNextPrev : nextTcb.queuePrev = some tid := by
                                    obtain ⟨_, hB, hP⟩ := hLink.1 tid tcb hTcbObj nextTid hNext
                                    rw [hNextTcbSt] at hB; cases hB; exact hP
                                  -- ObjInv chain
                                  have hObjInvSN := storeTcbQueueLinks_preserves_objects_invExt
                                    stPrev stNext nextTid _ _ _ hObjInv1 hStN
                                  have hPreEpSN : ∀ t : TCB, stNext.objects[endpointId]? ≠ some (.tcb t) := by
                                    intro t h
                                    rw [storeTcbQueueLinks_preserves_objects_ne stPrev stNext nextTid _ _ _
                                      endpointId hNeEpNext hObjInv1 hStN,
                                      storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _
                                      endpointId hNeEpPrev hObjInv hLinkP] at h
                                    exact absurd h (hPreEp t)
                                  have hObjInv4 := storeObject_preserves_objects_invExt' stNext endpointId _ pair4 hObjInvSN hStoreEpD
                                  -- Acyclicity
                                  -- prevTid.next changed: some tid → some nextTid.
                                  -- In st, path was prevTid → tid → nextTid → ...
                                  -- Now: prevTid → nextTid → ...  (shortcut)
                                  -- This cannot create cycles: any cycle through prevTid→nextTid in new state
                                  -- means nextTid →⁺ prevTid exists, but then in st: tid → nextTid →⁺ prevTid → tid = cycle.
                                  -- Use storeTcbQueueLinks_preserveNext for nextTid (queueNext preserved)
                                  -- and a custom argument for prevTid (queueNext changed but shortcutting)
                                  -- Acyclicity: stPrev shortcutted prevTid→tid→nextTid to prevTid→nextTid
                                  have hAcycSPrev : tcbQueueChainAcyclic stPrev := by
                                    intro tidC hp
                                    have hTransfer : ∀ a b, QueueNextPath stPrev a b → QueueNextPath st a b := by
                                      intro a b hp'
                                      induction hp' with
                                      | single x y tX hObjX hNxtX =>
                                        by_cases hxP : x.toObjId = prevTid.toObjId
                                        · have hPR := storeTcbQueueLinks_result_tcb st stPrev prevTid _ _ _ hObjInv hLinkP
                                          obtain ⟨origP, hOLkP, hPSP⟩ := hPR
                                          rw [hLookupP] at hOLkP; cases hOLkP
                                          rw [hxP] at hObjX; rw [hPSP] at hObjX; cases hObjX
                                          simp [tcbWithQueueLinks] at hNxtX
                                          -- hNxtX : tcb.queueNext = some y, hNext: tcb.queueNext = some nextTid
                                          have : some nextTid = some y := hNext ▸ hNxtX
                                          cases this -- y = nextTid
                                          exact .cons x tid nextTid prevTcb
                                            (by rw [hxP]; exact hPrevTcbObj)
                                            hPrevNextTid
                                            (.single tid nextTid tcb hTcbObj hNext)
                                        · exact .single x y tX
                                            (by rwa [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP] at hObjX)
                                            hNxtX
                                      | cons x y z tX hObjX hNxtX _ ih =>
                                        by_cases hxP : x.toObjId = prevTid.toObjId
                                        · have hPR := storeTcbQueueLinks_result_tcb st stPrev prevTid _ _ _ hObjInv hLinkP
                                          obtain ⟨origP, hOLkP, hPSP⟩ := hPR
                                          rw [hLookupP] at hOLkP; cases hOLkP
                                          rw [hxP] at hObjX; rw [hPSP] at hObjX; cases hObjX
                                          simp [tcbWithQueueLinks] at hNxtX
                                          -- hNxtX : tcb.queueNext = some y, hNext: tcb.queueNext = some nextTid
                                          have : some nextTid = some y := hNext ▸ hNxtX
                                          cases this -- y = nextTid
                                          exact .cons x tid z prevTcb
                                            (by rw [hxP]; exact hPrevTcbObj)
                                            hPrevNextTid
                                            (.cons tid nextTid z tcb hTcbObj hNext ih)
                                        · exact .cons x y z tX
                                            (by rwa [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP] at hObjX)
                                            hNxtX ih
                                    exact hAcyclic tidC (hTransfer tidC tidC hp)
                                  have hAcycSN := storeTcbQueueLinks_preserveNext_preserves_tcbQueueChainAcyclic
                                    stPrev stNext nextTid _ _ nextTcb.queueNext hObjInv1 hStN
                                    (fun t h => by rw [hLkN] at h; cases h; rfl) hAcycSPrev
                                  have hAcycEp4 := storeObject_nonTcb_preserves_tcbQueueChainAcyclic
                                    stNext pair4.2 endpointId _ (fun _ h => by cases h) hObjInvSN hStoreEpD hAcycSN
                                  have hAcycSF := storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic
                                    pair4.2 stF tid none none hObjInv4 hClearD hAcycEp4
                                  -- prevTid result in stPrev
                                  have hPrevResult := storeTcbQueueLinks_result_tcb st stPrev prevTid _ _ _ hObjInv hLinkP
                                  obtain ⟨origP, hOLkP, hPrevStPrev⟩ := hPrevResult
                                  rw [hLookupP] at hOLkP; cases hOLkP
                                  -- nextTid result in stNext
                                  have hNextResult := storeTcbQueueLinks_result_tcb stPrev stNext nextTid _ _ _ hObjInv1 hStN
                                  obtain ⟨origN, hOLkN, hNextStNext⟩ := hNextResult
                                  rw [hLkN] at hOLkN; cases hOLkN
                                  -- Transport helpers
                                  have hPreEpSt4 : ∀ t : TCB, pair4.2.objects[endpointId]? ≠ some (.tcb t) := by
                                    intro t h
                                    rw [storeObject_objects_eq stNext pair4.2 endpointId _ hObjInvSN hStoreEpD] at h; cases h
                                  -- TCB snapshots in stF
                                  -- prevTid in stF: unchanged from stPrev through stNext, pair4, then clearing tid
                                  have hPrevStF : stF.objects[prevTid.toObjId]? = some
                                      (.tcb (tcbWithQueueLinks prevTcb prevTcb.queuePrev prevTcb.queuePPrev tcb.queueNext)) := by
                                    rw [storeTcbQueueLinks_preserves_objects_ne pair4.2 stF tid _ _ _
                                      prevTid.toObjId hNePrevTid hObjInv4 hClearD,
                                      storeObject_objects_ne stNext pair4.2 endpointId prevTid.toObjId _
                                      hNeEpPrev.symm hObjInvSN hStoreEpD,
                                      storeTcbQueueLinks_preserves_objects_ne stPrev stNext nextTid _ _ _
                                      prevTid.toObjId hNePrevNext hObjInv1 hStN]
                                    exact hPrevStPrev
                                  -- nextTid in stF
                                  have hNextStF : stF.objects[nextTid.toObjId]? = some
                                      (.tcb (tcbWithQueueLinks nextTcb (some prevTid) (some (QueuePPrev.tcbNext prevTid)) nextTcb.queueNext)) := by
                                    rw [storeTcbQueueLinks_preserves_objects_ne pair4.2 stF tid _ _ _
                                      nextTid.toObjId hNeNextTid hObjInv4 hClearD,
                                      storeObject_objects_ne stNext pair4.2 endpointId nextTid.toObjId _
                                      hNeEpNext.symm hObjInvSN hStoreEpD]
                                    rw [hPrevSome] at hNextStNext; exact hNextStNext
                                  -- tid in stF
                                  have hTidResultF := storeTcbQueueLinks_result_tcb pair4.2 stF tid none none none hObjInv4 hClearD
                                  obtain ⟨_, _, hTidStF⟩ := hTidResultF
                                  -- Other TCBs transport
                                  have hFwdOtherD : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                      x.toObjId ≠ tid.toObjId → x.toObjId ≠ prevTid.toObjId → x.toObjId ≠ nextTid.toObjId →
                                      st.objects[x.toObjId]? = some (.tcb t) → stF.objects[x.toObjId]? = some (.tcb t) := by
                                    intro x t hxT hxP hxN ht
                                    rw [storeTcbQueueLinks_preserves_objects_ne pair4.2 stF tid _ _ _ x.toObjId hxT hObjInv4 hClearD,
                                        storeObject_objects_ne stNext pair4.2 endpointId x.toObjId _ ?_ hObjInvSN hStoreEpD,
                                        storeTcbQueueLinks_preserves_objects_ne stPrev stNext nextTid _ _ _ x.toObjId hxN hObjInv1 hStN,
                                        storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP]
                                    exact ht; intro h; rw [h] at ht; rw [hObj] at ht; cases ht
                                  have hBackOtherD : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                                      x.toObjId ≠ tid.toObjId → x.toObjId ≠ prevTid.toObjId → x.toObjId ≠ nextTid.toObjId →
                                      stF.objects[x.toObjId]? = some (.tcb t) → st.objects[x.toObjId]? = some (.tcb t) := by
                                    intro x t hxT hxP hxN ht
                                    have h4 : pair4.2.objects[x.toObjId]? = some (.tcb t) := by
                                      rwa [storeTcbQueueLinks_preserves_objects_ne pair4.2 stF tid _ _ _ x.toObjId hxT hObjInv4 hClearD] at ht
                                    have hSN : stNext.objects[x.toObjId]? = some (.tcb t) := by
                                      by_cases hx : x.toObjId = endpointId
                                      · rw [hx, storeObject_objects_eq stNext pair4.2 endpointId _ hObjInvSN hStoreEpD] at h4; cases h4
                                      · rwa [storeObject_objects_ne stNext pair4.2 endpointId x.toObjId _ hx hObjInvSN hStoreEpD] at h4
                                    have hSP : stPrev.objects[x.toObjId]? = some (.tcb t) := by
                                      rwa [storeTcbQueueLinks_preserves_objects_ne stPrev stNext nextTid _ _ _ x.toObjId hxN hObjInv1 hStN] at hSN
                                    rwa [storeTcbQueueLinks_preserves_objects_ne st stPrev prevTid _ _ _ x.toObjId hxP hObjInv hLinkP] at hSP
                                  -- Link integrity for stF (directly constructed)
                                  have hLinkStF : tcbQueueLinkIntegrity stF := by
                                    constructor
                                    · -- Forward: a.queueNext = some b ⟹ b exists ∧ b.queuePrev = some a
                                      intro a tcbA hA b hNxt
                                      by_cases haT : a.toObjId = tid.toObjId
                                      · -- a = tid: cleared, queueNext = none → contradiction
                                        rw [haT] at hA; rw [hTidStF] at hA; cases hA
                                        simp [tcbWithQueueLinks] at hNxt
                                      · by_cases haP : a.toObjId = prevTid.toObjId
                                        · -- a = prevTid: queueNext = tcb.queueNext = some nextTid
                                          rw [haP] at hA; rw [hPrevStF] at hA; cases hA
                                          simp [tcbWithQueueLinks] at hNxt
                                          -- hNxt : tcb.queueNext = some b
                                          rw [hNext] at hNxt; cases hNxt
                                          -- b = nextTid, need stF[nextTid] with queuePrev = some prevTid
                                          refine ⟨_, hNextStF, ?_⟩
                                          simp [tcbWithQueueLinks]
                                          exact (threadId_toObjId_injective haP.symm)
                                        · by_cases haN : a.toObjId = nextTid.toObjId
                                          · -- a = nextTid: queueNext = nextTcb.queueNext (unchanged)
                                            rw [haN] at hA; rw [hNextStF] at hA; cases hA
                                            simp [tcbWithQueueLinks] at hNxt
                                            -- hNxt : nextTcb.queueNext = some b
                                            obtain ⟨tcbB, hB, hP⟩ := hLink.1 nextTid nextTcb hNextTcbSt b hNxt
                                            by_cases hbT : b.toObjId = tid.toObjId
                                            · -- b = tid → tcb.queuePrev = some nextTid, but = some prevTid
                                              have hBT : st.objects[tid.toObjId]? = some (.tcb tcbB) := hbT ▸ hB
                                              rw [hTcbObj] at hBT; cases hBT
                                              rw [hPrevSome] at hP
                                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP)) hNePrevNext
                                            · by_cases hbP : b.toObjId = prevTid.toObjId
                                              · -- b = prevTid → return modified prevTid TCB
                                                have hBP : st.objects[prevTid.toObjId]? = some (.tcb tcbB) := hbP ▸ hB
                                                rw [hPrevTcbObj] at hBP
                                                have hTcbBEq := KernelObject.tcb.inj (Option.some.inj hBP)
                                                refine ⟨_, hbP ▸ hPrevStF, ?_⟩
                                                simp [tcbWithQueueLinks]
                                                rw [hTcbBEq, show a = nextTid from threadId_toObjId_injective haN]
                                                exact hP
                                              · by_cases hbN : b.toObjId = nextTid.toObjId
                                                · -- b = nextTid → nextTcb.queueNext = some nextTid → self-loop
                                                  have hBN : st.objects[nextTid.toObjId]? = some (.tcb tcbB) := hbN ▸ hB
                                                  rw [hNextTcbSt] at hBN; cases hBN
                                                  -- nextTcb.queueNext = some nextTid → self-loop → contradiction
                                                  rw [show b = nextTid from threadId_toObjId_injective hbN] at hNxt
                                                  exact absurd (.single nextTid nextTid nextTcb hNextTcbSt hNxt) (hAcyclic nextTid)
                                                · exact ⟨tcbB, hFwdOtherD b tcbB hbT hbP hbN hB,
                                                    hP.trans (congrArg some (threadId_toObjId_injective haN).symm)⟩
                                          · -- a = other: back-transport to st, use original link, forward-transport
                                            have hA' := hBackOtherD a tcbA haT haP haN hA
                                            obtain ⟨tcbB, hB, hP⟩ := hLink.1 a tcbA hA' b hNxt
                                            by_cases hbT : b.toObjId = tid.toObjId
                                            · -- b = tid: tcb.queuePrev = some a, but = some prevTid, a ≠ prevTid
                                              have hBT : st.objects[tid.toObjId]? = some (.tcb tcbB) := hbT ▸ hB
                                              rw [hTcbObj] at hBT; cases hBT
                                              rw [hPrevSome] at hP
                                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP).symm) haP
                                            · by_cases hbP : b.toObjId = prevTid.toObjId
                                              · -- b = prevTid: return modified prevTid TCB
                                                have hBP : st.objects[prevTid.toObjId]? = some (.tcb tcbB) := hbP ▸ hB
                                                rw [hPrevTcbObj] at hBP
                                                have hTcbBEq := KernelObject.tcb.inj (Option.some.inj hBP)
                                                refine ⟨_, hbP ▸ hPrevStF, ?_⟩
                                                simp [tcbWithQueueLinks]; rw [hTcbBEq]; exact hP
                                              · by_cases hbN : b.toObjId = nextTid.toObjId
                                                · -- b = nextTid: nextTcb.queuePrev = some tid, not some a
                                                  have hBN : st.objects[nextTid.toObjId]? = some (.tcb tcbB) := hbN ▸ hB
                                                  rw [hNextTcbSt] at hBN; cases hBN
                                                  rw [hNextPrev] at hP
                                                  exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP).symm) haT
                                                · exact ⟨tcbB, hFwdOtherD b tcbB hbT hbP hbN hB, hP⟩
                                    · -- Reverse: b.queuePrev = some a ⟹ a exists ∧ a.queueNext = some b
                                      intro b tcbB hB a hPrv
                                      by_cases hbT : b.toObjId = tid.toObjId
                                      · -- b = tid: cleared, queuePrev = none → contradiction
                                        rw [hbT] at hB; rw [hTidStF] at hB; cases hB
                                        simp [tcbWithQueueLinks] at hPrv
                                      · by_cases hbP : b.toObjId = prevTid.toObjId
                                        · -- b = prevTid: queuePrev = prevTcb.queuePrev (unchanged)
                                          rw [hbP] at hB; rw [hPrevStF] at hB; cases hB
                                          simp [tcbWithQueueLinks] at hPrv
                                          -- hPrv : prevTcb.queuePrev = some a
                                          obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 prevTid prevTcb hPrevTcbObj a hPrv
                                          by_cases haT : a.toObjId = tid.toObjId
                                          · -- a = tid: tcb.queueNext = some prevTid, but = some nextTid
                                            have hAT : st.objects[tid.toObjId]? = some (.tcb tcbA) := haT ▸ hA
                                            rw [hTcbObj] at hAT; cases hAT
                                            rw [hNext] at hNxt
                                            exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt)) hNePrevNext.symm
                                          · by_cases haP : a.toObjId = prevTid.toObjId
                                            · -- a = prevTid: prevTcb.queueNext = some prevTid, but = some tid
                                              have hAP : st.objects[prevTid.toObjId]? = some (.tcb tcbA) := haP ▸ hA
                                              rw [hPrevTcbObj] at hAP; cases hAP
                                              rw [hPrevNextTid] at hNxt
                                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt).symm) hNePrevTid
                                            · by_cases haN : a.toObjId = nextTid.toObjId
                                              · -- a = nextTid: return modified nextTid TCB
                                                have hAN : st.objects[nextTid.toObjId]? = some (.tcb tcbA) := haN ▸ hA
                                                rw [hNextTcbSt] at hAN; cases hAN
                                                refine ⟨_, haN ▸ hNextStF, ?_⟩
                                                simp [tcbWithQueueLinks]
                                                exact hNxt.trans (congrArg some (threadId_toObjId_injective hbP).symm)
                                              · exact ⟨tcbA, hFwdOtherD a tcbA haT haP haN hA,
                                                  hNxt.trans (congrArg some (threadId_toObjId_injective hbP).symm)⟩
                                        · by_cases hbN : b.toObjId = nextTid.toObjId
                                          · -- b = nextTid: queuePrev = some prevTid, so a = prevTid
                                            have hBN : stF.objects[nextTid.toObjId]? = some (.tcb tcbB) := hbN ▸ hB
                                            rw [hNextStF] at hBN
                                            have hTcbBEq := (KernelObject.tcb.inj (Option.some.inj hBN)).symm
                                            rw [hTcbBEq] at hPrv; simp [tcbWithQueueLinks] at hPrv
                                            -- hPrv : prevTid = a
                                            subst hPrv
                                            -- need stF[prevTid].queueNext = some nextTid
                                            refine ⟨_, hPrevStF, ?_⟩
                                            simp [tcbWithQueueLinks]
                                            rw [hNext]; exact congrArg some (threadId_toObjId_injective hbN.symm)
                                          · -- b = other: back-transport to st, use original link, forward-transport
                                            have hB' := hBackOtherD b tcbB hbT hbP hbN hB
                                            obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 b tcbB hB' a hPrv
                                            by_cases haT : a.toObjId = tid.toObjId
                                            · -- a = tid: tcb.queueNext = some b, but = some nextTid, b ≠ nextTid
                                              have hAT : st.objects[tid.toObjId]? = some (.tcb tcbA) := haT ▸ hA
                                              rw [hTcbObj] at hAT; cases hAT
                                              rw [hNext] at hNxt
                                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt).symm) hbN
                                            · by_cases haP : a.toObjId = prevTid.toObjId
                                              · -- a = prevTid: prevTcb.queueNext = some b, but = some tid, b ≠ tid
                                                have hAP : st.objects[prevTid.toObjId]? = some (.tcb tcbA) := haP ▸ hA
                                                rw [hPrevTcbObj] at hAP; cases hAP
                                                rw [hPrevNextTid] at hNxt
                                                exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt).symm) hbT
                                              · by_cases haN : a.toObjId = nextTid.toObjId
                                                · -- a = nextTid: return modified nextTid TCB
                                                  have hAN : st.objects[nextTid.toObjId]? = some (.tcb tcbA) := haN ▸ hA
                                                  rw [hNextTcbSt] at hAN; cases hAN
                                                  refine ⟨_, haN ▸ hNextStF, ?_⟩
                                                  simp [tcbWithQueueLinks]; exact hNxt
                                                · exact ⟨tcbA, hFwdOtherD a tcbA haT haP haN hA, hNxt⟩
                                  have hIqwfD : ∀ (qq : IntrusiveQueue), intrusiveQueueWellFormed qq st → intrusiveQueueWellFormed qq stF := by
                                    intro qq hWfQQ
                                    exact storeTcbQueueLinks_preserves_iqwf pair4.2 stF tid none none none hObjInv4 hClearD qq
                                      (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                        stNext pair4.2 endpointId _ hObjInvSN hStoreEpD hPreEpSN qq
                                        (storeTcbQueueLinks_preserves_iqwf stPrev stNext nextTid _ _ _ hObjInv1 hStN qq
                                          (storeTcbQueueLinks_preserves_iqwf st stPrev prevTid _ _ _ hObjInv hLinkP qq hWfQQ
                                            (fun hd hhd heq => by
                                              rw [(threadId_toObjId_injective heq)] at hhd
                                              obtain ⟨_, hT, hP⟩ := hWfQQ.2.1 prevTid hhd
                                              rw [hPrevTcbObj] at hT
                                              have := KernelObject.tcb.inj (Option.some.inj hT); rw [this]; exact hP)
                                            (fun tl htl heq => by
                                              rw [(threadId_toObjId_injective heq)] at htl
                                              obtain ⟨_, hT, hN⟩ := hWfQQ.2.2 prevTid htl
                                              rw [hPrevTcbObj] at hT
                                              have := KernelObject.tcb.inj (Option.some.inj hT)
                                              rw [← this] at hN; rw [hPrevNextTid] at hN; exact absurd hN (by simp)))
                                          (fun hd hhd heq => by
                                            rw [(threadId_toObjId_injective heq)] at hhd
                                            obtain ⟨_, hT, hP⟩ := hWfQQ.2.1 nextTid hhd
                                            rw [hNextTcbSt] at hT
                                            have hEq := KernelObject.tcb.inj (Option.some.inj hT)
                                            rw [← hEq] at hP; rw [hNextPrev] at hP; exact absurd hP (by simp))
                                          (fun tl htl heq => by
                                            rw [(threadId_toObjId_injective heq)] at htl
                                            obtain ⟨_, hT, hN⟩ := hWfQQ.2.2 nextTid htl
                                            rw [hNextTcbSt] at hT
                                            have := KernelObject.tcb.inj (Option.some.inj hT); rw [this]; exact hN)))
                                      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                                  have hEpWfD : ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
                                      stF.objects[epId']? = some (.endpoint ep') →
                                      dualQueueEndpointWellFormed epId' stF := by
                                    intro epId' ep' hObj'
                                    have hObjP4 := storeTcbQueueLinks_endpoint_backward pair4.2 stF tid none none none
                                      epId' ep' hObjInv4 hClearD hObj'
                                    unfold dualQueueEndpointWellFormed; rw [hObj']
                                    by_cases hNe : epId' = endpointId
                                    · -- Same endpoint: queue unchanged (head=q.head, tail=q.tail)
                                      rw [hNe] at hObjP4
                                      rw [storeObject_objects_eq stNext pair4.2 endpointId _ hObjInvSN hStoreEpD] at hObjP4
                                      cases hObjP4
                                      -- The stored endpoint has q' = {head=q.head, tail=q.tail} = q by η
                                      -- The stored queue q' = {head=q.head, tail=q.tail} = q by η
                                      -- So both sendQ and receiveQ of stored ep are original
                                      cases hRQ : isReceiveQ
                                      · -- isReceiveQ = false: sendQ modified (to q'), receiveQ unchanged
                                        simp only [Bool.false_eq_true, ↓reduceIte]
                                        refine ⟨hIqwfD _ ?_, hIqwfD ep.receiveQ hEpWf.2⟩
                                        rw [← hQ]; simp only [hRQ, Bool.false_eq_true, ↓reduceIte]; exact hEpWf.1
                                      · -- isReceiveQ = true: receiveQ modified (to q'), sendQ unchanged
                                        simp only [↓reduceIte]
                                        refine ⟨hIqwfD ep.sendQ hEpWf.1, hIqwfD _ ?_⟩
                                        rw [← hQ]; simp only [hRQ, ↓reduceIte]; exact hEpWf.2
                                    · -- Other endpoint: back-transport to original state
                                      have hObjSN : stNext.objects[epId']? = some (.endpoint ep') := by
                                        rwa [storeObject_objects_ne stNext pair4.2 endpointId epId' _ hNe hObjInvSN hStoreEpD] at hObjP4
                                      have hObjSP : stPrev.objects[epId']? = some (.endpoint ep') :=
                                        storeTcbQueueLinks_endpoint_backward stPrev stNext nextTid _ _ _ epId' ep' hObjInv1 hStN hObjSN
                                      have hObjOrig : st.objects[epId']? = some (.endpoint ep') :=
                                        storeTcbQueueLinks_endpoint_backward st stPrev prevTid _ _ _ epId' ep' hObjInv hLinkP hObjSP
                                      have hWfPre := hEpInv epId' ep' hObjOrig
                                      unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjOrig] at hWfPre
                                      exact ⟨hIqwfD ep'.sendQ hWfPre.1, hIqwfD ep'.receiveQ hWfPre.2⟩
                                  exact ⟨hEpWfD, hLinkStF, hAcycSF⟩

-- ============================================================================
-- V3-G6 (M-PRF-5): Primitive preservation for waitingThreadsPendingMessageNone
-- → Extracted to WaitingThreadHelpers.lean (available via import)
-- V3-G/I: Operation-level proofs (notificationSignal/Wait/Wake)
-- → Moved to NotificationPreservation.lean (available via import)
-- ============================================================================

-- ============================================================================
-- V3-G4: endpointQueuePopHead / endpointQueueEnqueue preservation
-- ============================================================================

/-- `endpointQueuePopHead` preserves `waitingThreadsPendingMessageNone`.
    PopHead only modifies the endpoint object (non-TCB) and TCB queue links;
    neither `ipcState` nor `pendingMessage` is changed for any thread. -/
theorem endpointQueuePopHead_preserves_waitingThreadsPendingMessageNone
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hInv : waitingThreadsPendingMessageNone st)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    waitingThreadsPendingMessageNone st' := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some htcb =>
          simp only []
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hInv1 := storeObject_nonTcb_preserves_waitingThreadsPendingMessageNone
              st pair.2 endpointId (.endpoint _) (fun tcb => by simp) hObjInv hStore hInv
            cases hNext : htcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                exact storeTcbQueueLinks_preserves_waitingThreadsPendingMessageNone
                  pair.2 st3 headTid none none none hObjInv1 hFinal hInv1
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hObjInv1 hLink
                  have hInv2 := storeTcbQueueLinks_preserves_waitingThreadsPendingMessageNone
                    pair.2 st2 nextTid _ _ _ hObjInv1 hLink hInv1
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, hEq⟩; subst hEq
                    exact storeTcbQueueLinks_preserves_waitingThreadsPendingMessageNone
                      st2 st3 headTid none none none hObjInv2 hFinal hInv2

/-- `endpointQueueEnqueue` preserves `waitingThreadsPendingMessageNone`.
    Enqueue only modifies the endpoint object (non-TCB) and TCB queue links;
    neither `ipcState` nor `pendingMessage` is changed for any thread. -/
theorem endpointQueueEnqueue_preserves_waitingThreadsPendingMessageNone
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (enqueueTid : SeLe4n.ThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hInv : waitingThreadsPendingMessageNone st)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st') :
    waitingThreadsPendingMessageNone st' := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st enqueueTid with
      | none => simp [hLookup] at hStep
      | some enqTcb =>
        simp only [hLookup] at hStep
        split at hStep
        · contradiction -- ipcState ≠ .ready
        · split at hStep
          · contradiction -- queue links check
          · -- Empty queue case
            split at hStep
            · -- tail = none
              split at hStep
              next => contradiction -- storeObject error
              next st1 hStore =>
                have hObjInv1 := storeObject_preserves_objects_invExt st st1 endpointId _ hObjInv hStore
                have hInv1 := storeObject_nonTcb_preserves_waitingThreadsPendingMessageNone
                  st st1 endpointId (.endpoint _) (fun tcb => by simp) hObjInv hStore hInv
                exact storeTcbQueueLinks_preserves_waitingThreadsPendingMessageNone
                  st1 st' enqueueTid _ _ _ hObjInv1 hStep hInv1
            · -- tail = some tailTid
              split at hStep
              next => contradiction -- lookupTcb tail = none
              next tailTcb _ =>
                split at hStep
                next => contradiction -- storeObject error
                next st1 hStore =>
                  have hObjInv1 := storeObject_preserves_objects_invExt st st1 endpointId _ hObjInv hStore
                  have hInv1 := storeObject_nonTcb_preserves_waitingThreadsPendingMessageNone
                    st st1 endpointId (.endpoint _) (fun tcb => by simp) hObjInv hStore hInv
                  split at hStep
                  next => contradiction -- storeTcbQueueLinks error
                  next st2 hLink1 =>
                    have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ _ _ _ _ hObjInv1 hLink1
                    have hInv2 := storeTcbQueueLinks_preserves_waitingThreadsPendingMessageNone
                      st1 st2 _ _ _ _ hObjInv1 hLink1 hInv1
                    exact storeTcbQueueLinks_preserves_waitingThreadsPendingMessageNone
                      st2 st' enqueueTid _ _ _ hObjInv2 hStep hInv2

-- ============================================================================
-- V3-G4: endpointSendDual / endpointReceiveDual preservation
-- ============================================================================

/-- `endpointSendDual` preserves `waitingThreadsPendingMessageNone`.
    Handshake path: popHead + storeTcbIpcStateAndMessage(.ready) + ensureRunnable.
    Block path: enqueue + storeTcbIpcStateAndMessage(.blockedOnSend) + removeRunnable.
    `.blockedOnSend` is outside the invariant scope (⇒ `True`), so both paths preserve. -/
theorem endpointSendDual_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : waitingThreadsPendingMessageNone st)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    waitingThreadsPendingMessageNone st' := by
  unfold endpointSendDual at hStep
  -- Eliminate bounds-check if-branches
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake path: popHead → storeTcbIpcStateAndMessage .ready → ensureRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId true st triple.2.2 triple.1 triple.2.1 hObjInv hPop
          have hInv1 := endpointQueuePopHead_preserves_waitingThreadsPendingMessageNone
            endpointId true st triple.2.2 triple.1 triple.2.1 hObjInv hInv hPop
          cases hMsg : storeTcbIpcStateAndMessage triple.2.2 triple.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInv2 := storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
              triple.2.2 st2 triple.1 .ready (some msg) hObjInv1 hMsg hInv1 trivial
            exact ensureRunnable_preserves_waitingThreadsPendingMessageNone _ _ hInv2
      | none =>
        -- Block path: enqueue → storeTcbIpcStateAndMessage .blockedOnSend → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
            endpointId false sender st st1 hObjInv hEnq
          have hInv1 := endpointQueueEnqueue_preserves_waitingThreadsPendingMessageNone
            endpointId false sender st st1 hObjInv hInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInv2 := storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
              st1 st2 sender (.blockedOnSend endpointId) (some msg) hObjInv1 hMsg hInv1 trivial
            exact removeRunnable_preserves_waitingThreadsPendingMessageNone _ _ hInv2

/-- `endpointReceiveDual` preserves `waitingThreadsPendingMessageNone`.
    Call path: sender→blockedOnReply(none) + receiver atomically set to .ready + senderMsg.
    Send path: sender→ready(none) + ensureRunnable + receiver atomically set to .ready + senderMsg.
    Block path: enqueue + receiver→blockedOnReceive + removeRunnable.
    AK1-D (I-M02): Dropped `hReceiverMsg` and `hReceiverNotBlocked` hypotheses
    after the operational rendezvous path was changed to atomically set
    receiver.ipcState := .ready alongside pendingMessage := senderMsg. The
    former hypothesis was needed to argue receiver's pre-state pendingMessage
    was `none`; the latter to exclude receiver being in a blocked state. Both
    become vacuous because the .ready post-state is unconstrained by
    `waitingThreadsPendingMessageNone`. Block path still requires
    `hReceiverMsg` via the embedded storeTcbIpcState + hPreLk argument. -/
theorem endpointReceiveDual_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : waitingThreadsPendingMessageNone st)
    (hReceiverMsg : ∀ tcb, lookupTcb st receiver = some tcb → tcb.pendingMessage = none)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    waitingThreadsPendingMessageNone st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInvPop := endpointQueuePopHead_preserves_objects_invExt
            endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hInvPop := endpointQueuePopHead_preserves_waitingThreadsPendingMessageNone
            endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hInv hPop
          -- Branch on senderWasCall
          cases hSenderIpc : pair.2.1.ipcState with
          | blockedOnCall _ =>
            simp only [hSenderIpc, ite_true] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hInvMsg := storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
                pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInvPop hMsg hInvPop trivial
              revert hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update; .ready falls through hTarget default
              cases hPend : storeTcbIpcStateAndMessage st2 receiver .ready _ with
              | ok st3 =>
                exact fun h => (Prod.mk.inj (Except.ok.inj h)).2 ▸
                  storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
                    st2 _ receiver .ready _ hObjInvMsg hPend hInvMsg trivial
              | error _ => simp
          | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
            simp only [hSenderIpc] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hInvMsg := storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
                pair.2.2 st2 pair.1 .ready none hObjInvPop hMsg hInvPop trivial
              have hInvEns := ensureRunnable_preserves_waitingThreadsPendingMessageNone st2 pair.1 hInvMsg
              have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by rwa [ensureRunnable_preserves_objects]
              revert hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update; .ready falls through hTarget default
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready _ with
              | ok st4 =>
                exact fun h => (Prod.mk.inj (Except.ok.inj h)).2 ▸
                  storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
                    _ st4 receiver .ready _ hObjInvEns hPend hInvEns trivial
              | error _ => simp
      | none =>
        -- Block path: cleanup → enqueue → storeTcbIpcState(.blockedOnReceive) → removeRunnable
        -- AI4-A: cleanupPreReceiveDonation before enqueue
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hInvClean := cleanupPreReceiveDonation_preserves_waitingThreadsPendingMessageNone st receiver hObjInv hInv
          have hReceiverMsgClean : ∀ tcb, lookupTcb (cleanupPreReceiveDonation st receiver) receiver = some tcb → tcb.pendingMessage = none := by
            -- AI4-A: cleanupPreReceiveDonation preserves pendingMessage on all TCBs.
            -- Backward transport through returnDonatedSchedContext which only modifies
            -- schedContextBinding, not pendingMessage.
            intro tcb' hLookup'
            have hTcb' := lookupTcb_some_objects _ _ _ hLookup'
            -- Backward transport of pendingMessage through cleanupPreReceiveDonation
            have hBack := cleanupPreReceiveDonation_frame_helper
              (P := fun s => s.objects[receiver.toObjId]? = some (.tcb tcb') →
                ∃ tcb₀, st.objects[receiver.toObjId]? = some (.tcb tcb₀) ∧
                  tcb₀.pendingMessage = tcb'.pendingMessage)
              st receiver (fun h => ⟨tcb', h, rfl⟩)
              (fun scId owner st₁ hRet hTcb₁ => by
                obtain ⟨tcb₀, hTcb₀, _, _, _, hMsg₀⟩ :=
                  returnDonatedSchedContext_tcb_queue_backward st st₁ receiver scId owner hObjInv hRet
                    receiver.toObjId tcb' hTcb₁
                exact ⟨tcb₀, hTcb₀, hMsg₀⟩)
              hTcb'
            obtain ⟨tcb₀, hTcb₀, hMsg₀⟩ := hBack
            -- Reconstruct lookupTcb for original state
            have hNotRes : ¬receiver.isReserved = true := by
              intro hRes; simp [lookupTcb, hRes] at hLookup'
            have hOrig : lookupTcb st receiver = some tcb₀ := by
              unfold lookupTcb; simp [hNotRes]; split
              next t hObj => rw [hTcb₀] at hObj; cases hObj; rfl
              next hNone => rw [hTcb₀] at hNone; simp at hNone
            rw [← hMsg₀]; exact hReceiverMsg tcb₀ hOrig
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInvEnq := endpointQueueEnqueue_preserves_objects_invExt
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hInvEnq := endpointQueueEnqueue_preserves_waitingThreadsPendingMessageNone
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hInvClean hEnq
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hInv2 := storeTcbIpcState_preserves_waitingThreadsPendingMessageNone
                st1 st2 receiver (.blockedOnReceive endpointId) hObjInvEnq hIpc hInvEnq (by
                  intro tcb₂ hLk₂
                  -- Receiver's pendingMessage is preserved from pre-state through enqueue.
                  -- Extract objects lookup from lookupTcb
                  have hNotRes₂ : ¬receiver.isReserved = true := by
                    intro hRes; simp [lookupTcb, hRes] at hLk₂
                  have hObjLk₂ : st1.objects[receiver.toObjId]? = some (.tcb tcb₂) := by
                    unfold lookupTcb at hLk₂; split at hLk₂
                    · simp at hLk₂
                    · split at hLk₂
                      next t hObj => exact Option.some.inj hLk₂ ▸ hObj
                      all_goals simp at hLk₂
                  -- Use backward pendingMessage lemma through endpointQueueEnqueue
                  obtain ⟨preTcb₂, hPreTcb₂, hMsgEq⟩ := endpointQueueEnqueue_tcb_pendingMessage_backward
                    endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 receiver tcb₂ hObjInvClean hEnq hObjLk₂
                  -- Connect to hReceiverMsgClean: preTcb₂.pendingMessage = none
                  have hPreLk₂ : lookupTcb (cleanupPreReceiveDonation st receiver) receiver = some preTcb₂ := by
                    unfold lookupTcb; simp [hNotRes₂]; split
                    next t hObj => rw [hPreTcb₂] at hObj; cases hObj; rfl
                    next hNone => rw [hPreTcb₂] at hNone; simp at hNone
                  rw [← hMsgEq]; exact hReceiverMsgClean preTcb₂ hPreLk₂)
              exact removeRunnable_preserves_waitingThreadsPendingMessageNone _ _ hInv2

-- ============================================================================
-- V3-G4: endpointCall preservation
-- ============================================================================

/-- `endpointCall` preserves `waitingThreadsPendingMessageNone`.
    Handshake path: popHead + storeTcbIpcStateAndMessage(.ready, msg) + ensureRunnable
      + storeTcbIpcState(.blockedOnReply) + removeRunnable.
    Block path: enqueue + storeTcbIpcStateAndMessage(.blockedOnCall, msg) + removeRunnable.
    All ipcState transitions are to non-receiver-blocking states, so hTarget is trivial. -/
theorem endpointCall_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : waitingThreadsPendingMessageNone st)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    waitingThreadsPendingMessageNone st' := by
  unfold endpointCall at hStep
  -- Eliminate message bounds checks
  split at hStep
  · simp at hStep
  · split at hStep
    · simp at hStep
    · cases hObj : st.objects[endpointId]? with
      | none => simp [hObj] at hStep
      | some obj => cases obj with
        | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
        | endpoint ep =>
          simp only [hObj] at hStep
          cases hHead : ep.receiveQ.head with
          | some _ =>
            -- Handshake path: popHead + storeTcbIpcStateAndMessage(.ready) + ensureRunnable
            --   + storeTcbIpcState(.blockedOnReply) + removeRunnable
            cases hPop : endpointQueuePopHead endpointId true st with
            | error e => simp [hHead, hPop] at hStep
            | ok pair =>
              simp only [hHead, hPop] at hStep
              have hObjInvPop := endpointQueuePopHead_preserves_objects_invExt
                endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
              have hInvPop := endpointQueuePopHead_preserves_waitingThreadsPendingMessageNone
                endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hInv hPop
              cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
              | error e => simp [hMsg] at hStep
              | ok st1 =>
                simp only [hMsg] at hStep
                have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt
                  pair.2.2 st1 pair.1 _ _ hObjInvPop hMsg
                have hInv1 := storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
                  pair.2.2 st1 pair.1 .ready (some msg) hObjInvPop hMsg hInvPop trivial
                have hInvEns := ensureRunnable_preserves_waitingThreadsPendingMessageNone st1 pair.1 hInv1
                have hObjInvEns : (ensureRunnable st1 pair.1).objects.invExt := by
                  rwa [ensureRunnable_preserves_objects]
                -- AK1-C (I-M01): storeTcbIpcStateAndMessage atomically clears caller's pendingMessage
                cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st1 pair.1) caller
                    (.blockedOnReply endpointId (some pair.1)) none with
                | error e => simp [hIpc] at hStep
                | ok st2 =>
                  simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, hEq⟩ := hStep; subst hEq
                  have hInv2 := storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
                    _ st2 caller (.blockedOnReply endpointId (some pair.1)) none
                    hObjInvEns hIpc hInvEns trivial
                  exact removeRunnable_preserves_waitingThreadsPendingMessageNone _ _ hInv2
          | none =>
            -- Block path: enqueue + storeTcbIpcStateAndMessage(.blockedOnCall) + removeRunnable
            cases hEnq : endpointQueueEnqueue endpointId false caller st with
            | error e => simp [hHead, hEnq] at hStep
            | ok st1 =>
              simp only [hHead, hEnq] at hStep
              have hObjInvEnq := endpointQueueEnqueue_preserves_objects_invExt
                endpointId false caller st st1 hObjInv hEnq
              have hInvEnq := endpointQueueEnqueue_preserves_waitingThreadsPendingMessageNone
                endpointId false caller st st1 hObjInv hInv hEnq
              cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
              | error e => simp [hMsg] at hStep
              | ok st2 =>
                simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                have hInv2 := storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
                  st1 st2 caller (.blockedOnCall endpointId) (some msg)
                  hObjInvEnq hMsg hInvEnq trivial
                exact removeRunnable_preserves_waitingThreadsPendingMessageNone _ _ hInv2

-- ============================================================================
-- V3-G: endpointReply preservation
-- ============================================================================

/-- `endpointReply` preserves `waitingThreadsPendingMessageNone`.
    Reply sets replyTarget's ipcState from `.blockedOnReply` to `.ready` with
    `pendingMessage := some msg`, then `ensureRunnable`. Both `.blockedOnReply`
    and `.ready` are unconstrained states, so the target case is trivial.
    Other threads: frame reasoning via storeTcbIpcStateAndMessage + ensureRunnable. -/
theorem endpointReply_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : waitingThreadsPendingMessageNone st)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    waitingThreadsPendingMessageNone st' := by
  unfold endpointReply at hStep
  -- Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  -- lookupTcb
  cases hLk : lookupTcb st target with
  | none => simp [hLk] at hStep
  | some tcb =>
    simp only [hLk] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLk] at hStep
    -- ipcState match — only blockedOnReply proceeds
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      -- AK1-B (I-H02): Fail-closed on replyTarget = none
      suffices ∀ st1, storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st1 →
          waitingThreadsPendingMessageNone (ensureRunnable st1 target) by
        cases replyTarget with
        | none => simp at hStep
        | some expected =>
          simp only at hStep
          split at hStep
          · -- authorized = true
            revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
            | error e => simp
            | ok st1 =>
              intro hEq; cases hEq
              exact this st1 hMsg
          · simp_all
      intro st1 hMsg
      exact ensureRunnable_preserves_waitingThreadsPendingMessageNone _ _
        (storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
          st st1 target .ready (some msg) hObjInv hMsg hInv trivial)

-- ============================================================================
-- V3-G5: endpointReplyRecv preservation
-- ============================================================================

/-- `endpointReplyRecv` preserves `waitingThreadsPendingMessageNone`.
    Reply phase: storeTcbIpcStateAndMessage(.ready, msg) on replyTarget + ensureRunnable.
    Receive phase: delegates to endpointReceiveDual.
    Requires `hNeq` (receiver ≠ replyTarget) so the reply phase does not change
    receiver's TCB, allowing receiver preconditions to propagate unchanged. -/
theorem endpointReplyRecv_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : waitingThreadsPendingMessageNone st)
    (hNeq : receiver.toObjId ≠ replyTarget.toObjId)
    (hReceiverMsg : ∀ tcb, lookupTcb st receiver = some tcb → tcb.pendingMessage = none)
    (hReceiverNotBlocked : ∀ tcb, lookupTcb st receiver = some tcb →
      match tcb.ipcState with
      | .blockedOnReceive _ => False
      | .blockedOnNotification _ => False
      | _ => True)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    waitingThreadsPendingMessageNone st' := by
  unfold endpointReplyRecv at hStep
  -- Eliminate message bounds checks
  split at hStep
  · simp at hStep
  · split at hStep
    · simp at hStep
    · cases hLookup : lookupTcb st replyTarget with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
        cases hIpc : tcb.ipcState with
        | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _
          | blockedOnCall _ => simp [hIpc] at hStep
        | blockedOnReply _ expectedReplier =>
          simp only [hIpc] at hStep
          -- Use suffices to factor out authorization check handling
          suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
              (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
                waitingThreadsPendingMessageNone stR.2) by
            -- AK1-B (I-H02): Fail-closed on expectedReplier = none
            cases expectedReplier with
            | none => simp at hStep
            | some expected =>
              simp only at hStep
              split at hStep
              · revert hStep
                cases hStore : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
                | error e => simp
                | ok st1 =>
                  simp only []
                  cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
                  | error e => simp
                  | ok result =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact this st1 hStore result hRecv
              · simp_all
          -- Prove the core invariant preservation
          intro st1 hStore stR hRecv
          have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt
            st st1 replyTarget _ _ hObjInv hStore
          have hInv1 := storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
            st st1 replyTarget .ready (some msg) hObjInv hStore hInv trivial
          have hInvEns := ensureRunnable_preserves_waitingThreadsPendingMessageNone
            st1 replyTarget hInv1
          have hObjInvEns : (ensureRunnable st1 replyTarget).objects.invExt := by
            rwa [ensureRunnable_preserves_objects]
          -- Frame: receiver's TCB unchanged through reply phase (receiver ≠ replyTarget)
          have hReceiverFrame : ∀ tcb', lookupTcb (ensureRunnable st1 replyTarget) receiver = some tcb' →
              lookupTcb st receiver = some tcb' := by
            intro tcb' hLk'
            have hLk1 : lookupTcb st1 receiver = some tcb' := by
              unfold lookupTcb at hLk' ⊢; rw [ensureRunnable_preserves_objects] at hLk'; exact hLk'
            have hNotRes : ¬receiver.isReserved = true := by
              intro hRes; simp [lookupTcb, hRes] at hLk'
            have hObjLk1 : st1.objects[receiver.toObjId]? = some (.tcb tcb') := by
              unfold lookupTcb at hLk1; split at hLk1
              · simp at hLk1
              · split at hLk1
                next t hObj => exact Option.some.inj hLk1 ▸ hObj
                all_goals simp at hLk1
            have hFrame := storeTcbIpcStateAndMessage_preserves_objects_ne
              st st1 replyTarget _ _ receiver.toObjId hNeq hObjInv hStore
            rw [hFrame] at hObjLk1
            unfold lookupTcb; simp [hNotRes]; split
            next t hObj => rw [hObjLk1] at hObj; cases hObj; rfl
            next hNone => rw [hObjLk1] at hNone; simp at hNone
          -- AK1-D: hReceiverNotBlocked dropped from endpointReceiveDual_preserves_waitingThreadsPendingMessageNone
          exact endpointReceiveDual_preserves_waitingThreadsPendingMessageNone
            _ stR.2 endpointId receiver stR.1 hObjInvEns hInvEns
            (fun tcb' hLk' => hReceiverMsg tcb' (hReceiverFrame tcb' hLk'))
            (by have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)


end SeLe4n.Kernel
