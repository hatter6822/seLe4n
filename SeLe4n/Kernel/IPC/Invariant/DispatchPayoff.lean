-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.IPC.CrossCore.DispatchInvariant
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatchInvariant
import SeLe4n.Kernel.IPC.Invariant.Reachability

/-!
# The dispatch-tier `ipcInvariantFull` payoffs

The two theorems the de-threading closure exists to make possible:
`dispatchWithCap_preserves_ipcInvariantFull` — the bundle carried across every
syscall the capability dispatcher routes — and
`dispatchSyscall_preserves_ipcInvariantFull`, the same fact one tier up at the
kernel's syscall entry, through the capability resolution and the taint
application.

**Staged, deliberately**: the `.call` arm composes
`endpointCallCrossCoreDispatch_preserves_ipcInvariantFull`
(`IPC/CrossCore/DispatchInvariant.lean`), which is staged with the
`EndpointCallInvariant` surface it reads; a payoff quantifying over that arm
cannot state in production until the call surface moves.  Everything else this
module builds on is production.  CI builds this module on every PR through
`Platform.Staged`.

The hypothesis surface is `syscallDispatchQuiescence`: `ipcReachable` (the
state-shaped preconditions of the whole de-threaded family), the running
caller's shape, and the per-arm facts the RR3.15–RR3.21 packs need — every
field a pre-state fact, so nothing is bound on the post-state.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

-- ============================================================================
-- §1  `resolveExtraCaps` — CDT-only writes, badge-valid outputs
-- ============================================================================

private theorem ensureCdtNodeForSlotChecked_scheduler_eq
    (st : SystemState) (ref : SlotRef) (node : CdtNodeId) (st' : SystemState)
    (h : SystemState.ensureCdtNodeForSlotChecked st ref = some (node, st')) :
    st'.scheduler = st.scheduler := by
  unfold SystemState.ensureCdtNodeForSlotChecked at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

/-- Resolution mints CDT nodes only: objects and scheduler are framed, and
every resolved capability's badge is valid, because each one is read out of a
CNode slot of a state whose store is the pre-state's. -/
private theorem resolveExtraCaps_shape
    (cspaceRoot : SeLe4n.ObjId) (capAddrs : Array SeLe4n.CPtr) (depth : Nat)
    (granted : Bool) (st : SystemState)
    (hCapWf : capabilityBadgesWellFormed st) :
    (resolveExtraCaps cspaceRoot capAddrs depth granted st).2.objects = st.objects ∧
    (resolveExtraCaps cspaceRoot capAddrs depth granted st).2.scheduler = st.scheduler ∧
    (∀ (i : Nat) (c : TransferCap),
      (resolveExtraCaps cspaceRoot capAddrs depth granted st).1[i]? = some c →
      ∀ b, c.cap.badge = some b → b.valid) := by
  unfold resolveExtraCaps
  split
  · exact ⟨rfl, rfl, fun i c hc => by cases hc⟩
  · refine Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Array TransferCap × SystemState) =>
        acc.2.objects = st.objects ∧ acc.2.scheduler = st.scheduler ∧
        (∀ (i : Nat) (c : TransferCap), acc.1[i]? = some c →
          ∀ b, c.cap.badge = some b → b.valid))
      ⟨rfl, rfl, fun i c hc => by cases hc⟩ ?_
    intro i acc hAcc
    obtain ⟨hO, hS, hB⟩ := hAcc
    split
    · exact ⟨hO, hS, hB⟩
    · rename_i ref hRes
      split
      · exact ⟨hO, hS, hB⟩
      · rename_i cap hLk
        split
        · exact ⟨hO, hS, hB⟩
        · rename_i node stNode hNode
          have hCapWfAcc : capabilityBadgesWellFormed acc.2 := by
            intro oid cn slot c b hCn hLk2 hB2
            rw [hO] at hCn
            exact hCapWf oid cn slot c b hCn hLk2 hB2
          refine ⟨(SystemState.ensureCdtNodeForSlotChecked_objects_eq acc.2 ref node
              stNode hNode).trans hO,
            (ensureCdtNodeForSlotChecked_scheduler_eq acc.2 ref node stNode
              hNode).trans hS, ?_⟩
          intro j c hc b hBadge
          rw [Array.getElem?_push] at hc
          split at hc
          · obtain rfl : ({ cap := cap, srcNode := node } : TransferCap) = c :=
              Option.some.inj hc
            exact lookupSlotCap_badge_valid acc.2 ref cap hCapWfAcc hLk b hBadge
          · exact hB j c hc b hBadge

-- ============================================================================
-- §2  The reply leg's relaxed bundle upgrades when no donation names the caller
-- ============================================================================

/-- When no thread's binding names `woken` as its donation owner, the relaxed
bundle's escape clause is unused and the full bundle holds. -/
private theorem ipcInvariantFull_of_exceptDonationOwner_of_no_edge
    (st : SystemState) (woken : SeLe4n.ThreadId)
    (hExc : ipcInvariantFullExceptDonationOwner st woken)
    (hNoEdge : ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc0 : SeLe4n.SchedContextId),
      st.objects[s.toObjId]? = some (.tcb sTcb) →
      sTcb.schedContextBinding ≠ .donated sc0 woken) :
    ipcInvariantFull st := by
  obtain ⟨hIpc, hDual, hBnd, hBadge, hBTPM, hNoDup, hQMC, hQNBC, hQHBC, hBTT,
    hDCA, hDOVexc, hPSI, hDBT, hBRT, hRCL, hPRR, hDOU, hEQTB, hQNTB⟩ := hExc
  refine ⟨hIpc, hDual, hBnd, hBadge, hBTPM, hNoDup, hQMC, hQNBC, hQHBC, hBTT,
    hDCA, ?_, hPSI, hDBT, hBRT, hRCL, hPRR, hDOU, hEQTB, hQNTB⟩
  intro tid tcb scId owner hT hB
  obtain ⟨hSC, ownerTcb, hOT, hOU, hDisj⟩ := hDOVexc tid tcb scId owner hT hB
  refine ⟨hSC, ownerTcb, hOT, hOU, ?_⟩
  rcases hDisj with rfl | hBlocked
  · exact absurd hB (hNoEdge tid tcb scId hT)
  · exact hBlocked

-- ============================================================================
-- §3  `replyRecvBody` — the `.replyRecv` three-stage composite
-- ============================================================================

/-- **`.replyRecv`'s composite bundle**: reply leg (relaxed at the woken
caller, upgraded by the no-donation-edge confinement), receive leg, donation
return, and both return-frame stagers.

The mid-stage hypotheses are quantified over each stage's committed state —
pre-state-computable expressions, dischargeable before the step; the
donated-server path (a live donation edge naming the woken caller) is outside
this bundle's confinement and registered follow-up work on the reply chain's
own composite surface. -/
theorem replyRecvBody_preserves_ipcInvariantFull
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (ec : CoreId) (st stOut : SystemState) (summary : CapTransferSummary)
    (hReach : ipcReachable st)
    (hNoEdge1 : ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc0 : SeLe4n.SchedContextId),
      ((endpointReplyOnCore tid prevCaller msg ec st).1).objects[s.toObjId]?
        = some (.tcb sTcb) →
      sTcb.schedContextBinding ≠ .donated sc0 prevCaller)
    (hReceiverReady1 : ∃ tcb : TCB,
      ((endpointReplyOnCore tid prevCaller msg ec st).1).getTcb? tid = some tcb ∧
      tcb.ipcState = .ready)
    (hBudgets1 : allTimeoutBudgetsNone (endpointReplyOnCore tid prevCaller msg ec st).1)
    (hReplyIdValid1 : replyIdEstablishFresh (endpointReplyOnCore tid prevCaller msg ec st).1 rid)
    (hCapBadges1 : ∀ (tcb : TCB),
      (endpointReceiveDualOnCore epId tid (some rid) ec
          (endpointReplyOnCore tid prevCaller msg ec st).1).1.getTcb? tid = some tcb →
      ∀ m, tcb.pendingMessage = some m →
      ∀ (i : Nat) (c : TransferCap), m.caps[i]? = some c →
        ∀ b, c.cap.badge = some b → b.valid)
    (hReturnStage : ∀ (nextThread : SeLe4n.ThreadId)
        (summary2 : CapTransferSummary) (sgi2 : Option (CoreId × Concurrency.SgiKind))
        (st2 : SystemState),
      endpointReceiveDualWithCapsOnCore epId tid (some rid) receiverCspaceRoot
          receiverSlotBase ec (endpointReplyOnCore tid prevCaller msg ec st).1
        = (st2, .ok (nextThread, summary2, sgi2)) →
      st2.objects.invExt ∧
      (∀ tcb, st2.getTcb? ((recordedReplyServer? st prevCaller).getD tid) = some tcb →
        passiveServerIdleAllowed tcb.ipcState) ∧
      (∀ (tid' : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
        st2.getTcb? tid' = some tcb → tcb.schedContextBinding ≠ .donated scId tid) ∧
      (∀ st3, replyRecvReturnDonation tid ((recordedReplyServer? st prevCaller).getD tid)
          nextThread (determineExecutingCore st ((recordedReplyServer? st prevCaller).getD tid))
          st2 = .ok ((), st3) →
        st3.objects.invExt))
    (hStep : replyRecvBody epId tid rid prevCaller msg receiverCspaceRoot
      receiverSlotBase ec st = .ok (summary, stOut)) :
    ipcInvariantFull stOut ∧ stOut.objects.invExt := by
  unfold replyRecvBody at hStep
  dsimp only [] at hStep
  have hExc1 := endpointReplyOnCore_preserves_ipcInvariantFullExceptDonationOwner tid
    prevCaller msg ec st hReach.ipcInvariantFull hReach.objects_invExt
    hReach.allTimeoutBudgetsNone
  have hObjInv1 := endpointReplyOnCore_preserves_objects_invExt tid prevCaller msg ec st
    hReach.objects_invExt
  have hInv1 : ipcInvariantFull (endpointReplyOnCore tid prevCaller msg ec st).1 :=
    ipcInvariantFull_of_exceptDonationOwner_of_no_edge _ prevCaller hExc1 hNoEdge1
  cases hReply : endpointReplyOnCore tid prevCaller msg ec st with
  | mk st1 res1 =>
      rw [hReply] at hStep hInv1 hObjInv1 hReceiverReady1 hBudgets1 hReplyIdValid1 hCapBadges1 hReturnStage
      cases res1 with
      | error e => simp only [] at hStep; cases hStep
      | ok u =>
          simp only [] at hStep
          obtain ⟨tcbR, hT1, hReadyR⟩ := hReceiverReady1
          have hT1obj := (SystemState.getTcb?_eq_some_iff st1 tid tcbR).mp hT1
          have hFresh1 := readyThread_endpointQueueFresh st1 tid tcbR
            hInv1.queueHeadBlockedConsistent hInv1.endpointQueueTailBlockedConsistent
            hT1obj hReadyR
          have hTail1 := recvTailCrossQueueFresh st1 epId
            hInv1.dualQueueSystemInvariant hInv1.endpointQueueTailBlockedConsistent
          have hInv2 := endpointReceiveDualWithCapsOnCore_preserves_ipcInvariantFull
            epId tid (some rid) receiverCspaceRoot receiverSlotBase ec st1
            hInv1 hObjInv1 hBudgets1 hFresh1 hTail1
            (fun r hr => by obtain rfl := Option.some.inj hr; exact hReplyIdValid1)
            (fun tcb hTcb => by
              rw [hT1] at hTcb
              obtain rfl := Option.some.inj hTcb
              exact readyThread_notBlockedOnReceive tcbR hReadyR)
            (fun tcb hTcb => by
              rw [hT1] at hTcb
              obtain rfl := Option.some.inj hTcb
              exact hReadyR)
            hCapBadges1
          cases hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid)
              receiverCspaceRoot receiverSlotBase ec st1 with
          | mk st2 res2 =>
              rw [hRecv] at hStep hInv2
              cases res2 with
              | error e => simp only [] at hStep; cases hStep
              | ok triple =>
                  obtain ⟨nextThread, summary2, sgi2⟩ := triple
                  simp only [] at hStep
                  obtain ⟨hObjInv2, hSrvIdle2, hNotOwner2, hObjInv3f⟩ :=
                    hReturnStage nextThread summary2 sgi2 st2 hRecv
                  cases hRet : replyRecvReturnDonation tid
                      ((recordedReplyServer? st prevCaller).getD tid) nextThread
                      (determineExecutingCore st
                        ((recordedReplyServer? st prevCaller).getD tid)) st2 with
                  | error e => rw [hRet] at hStep; cases hStep
                  | ok pair3 =>
                      obtain ⟨u3, st3⟩ := pair3; cases u3
                      rw [hRet] at hStep
                      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                      obtain ⟨rfl, hOut⟩ := hStep
                      have hInv3 := replyRecvReturnDonation_preserves_ipcInvariantFull
                        tid ((recordedReplyServer? st prevCaller).getD tid) nextThread
                        (determineExecutingCore st
                          ((recordedReplyServer? st prevCaller).getD tid))
                        st2 st3 () hObjInv2 hInv2 hSrvIdle2 hNotOwner2 hRet
                      have hObjInv3 := hObjInv3f st3 hRet
                      have hInvD := stageDeliveredMessage_preserves_ipcInvariantFull st3
                        prevCaller 0 hObjInv3 hInv3
                      have hObjInvD := stageDeliveredMessage_objects_invExt st3
                        prevCaller 0 hObjInv3
                      rw [← hOut]
                      exact ⟨stageWokenSendCompletion_preserves_ipcInvariantFull _ _
                          hObjInvD hInvD,
                        stageWokenSendCompletion_objects_invExt _ _ hObjInvD⟩

-- ============================================================================
-- §4  The `dispatchWithCap` payoff
-- ============================================================================

/-- The pre-state quiescence facts `dispatchWithCap`'s own arms consume, on
top of the capability-only tier's pack.  Every field is a pre-state fact —
several quantify over a stage's committed state, which is a pre-state-computable
expression — so the payoff binds nothing on the post-state. -/
structure syscallDispatchQuiescence (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState) : Prop where
  reachable : ipcReachable st
  capOnly : capabilityDispatchQuiescence decoded cap st
  callerShape : ∃ tcb : TCB, st.getTcb? tid = some tcb ∧ tcb.ipcState = .ready ∧
    tcb.schedContextBinding ≠ .unbound
  mintBadgeValid : ∀ args, decoded.syscallId = .cspaceMint →
    decodeCSpaceMintArgs decoded = .ok args → args.badge.valid
  sendStage : ∀ epId, decoded.syscallId = .send → cap.target = .object epId →
    ∀ st1 res, endpointSendDualWithCapsOnCore epId tid
      { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
        caps := (resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
          gate.capDepth (cap.rights.mem .grant) st).1,
        badge := cap.badge, capsGranted := cap.rights.mem .grant } cap.rights
      gate.cspaceRoot decoded.capRecvSlot
      (determineExecutingCore (resolveExtraCaps gate.cspaceRoot
        (decodeExtraCapAddrs decoded) gate.capDepth (cap.rights.mem .grant) st).2 tid)
      (resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded) gate.capDepth
        (cap.rights.mem .grant) st).2 = (st1, res) →
    st1.objects.invExt
  callStage : ∀ epId, decoded.syscallId = .call → cap.target = .object epId →
    ∀ st1 res, endpointCallCrossCoreDispatch epId tid
      { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
        caps := (resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
          gate.capDepth (cap.rights.mem .grant) st).1,
        badge := cap.badge, capsGranted := cap.rights.mem .grant } cap.rights
      gate.cspaceRoot decoded.capRecvSlot
      (determineExecutingCore (resolveExtraCaps gate.cspaceRoot
        (decodeExtraCapAddrs decoded) gate.capDepth (cap.rights.mem .grant) st).2 tid)
      (resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded) gate.capDepth
        (cap.rights.mem .grant) st).2 = (st1, res) →
    st1.objects.invExt
  callNotSelfRendezvous : ∀ epId, decoded.syscallId = .call → cap.target = .object epId →
    ∀ ep receiverTid, st.getEndpoint? epId = some ep →
      ep.receiveQ.head = some receiverTid → tid ≠ receiverTid
  recvStage : ∀ epId replyIdOpt, decoded.syscallId = .receive →
    cap.target = .object epId →
    resolveRecvReplyId gate decoded st = .ok replyIdOpt →
    (∀ rid, replyIdOpt = some rid → replyIdEstablishFresh st rid) ∧
    (∀ (tcb : TCB),
      (endpointReceiveDualOnCore epId tid replyIdOpt
          (determineExecutingCore st tid) st).1.getTcb? tid = some tcb →
      ∀ m, tcb.pendingMessage = some m →
      ∀ (i : Nat) (c : TransferCap), m.caps[i]? = some c →
        ∀ b, c.cap.badge = some b → b.valid) ∧
    (∀ st1 res, endpointReceiveDualWithCapsOnCore epId tid replyIdOpt gate.cspaceRoot
        decoded.capRecvSlot (determineExecutingCore st tid) st = (st1, res) →
      st1.objects.invExt)
  replyStage : ∀ rid (r : Reply) (callerTid : SeLe4n.ThreadId),
    decoded.syscallId = .reply → cap.target = .replyCap rid →
    st.getReply? rid = some r → r.caller = some callerTid →
    (∀ expected, recordedReplyServer? st callerTid = some expected →
      (∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
        st.objects[s.toObjId]? = some (.tcb sTcb) →
        sTcb.schedContextBinding = .donated sc callerTid →
        replyDonationReturn? st expected = some (sc, callerTid)) ∧
      (∀ tcb, st.getTcb? expected = some tcb → passiveServerIdleAllowed tcb.ipcState)) ∧
    (∀ st1 res, endpointReplyCrossCoreDispatch tid callerTid
        { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
          caps := #[], badge := cap.badge } (determineExecutingCore st tid) st
        = (st1, res) →
      st1.objects.invExt)
  signalNoBoundTarget : ∀ notifId, decoded.syscallId = .notificationSignal →
    cap.target = .object notifId → boundDeliveryTarget? st notifId = none
  replyRecvStage : ∀ rid prevCaller replyBadge epId,
    decoded.syscallId = .replyRecv → cap.target = .object epId →
    resolveReplyRecvReply gate decoded st = .ok (rid, prevCaller, replyBadge) →
    (∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc0 : SeLe4n.SchedContextId),
      ((endpointReplyOnCore tid prevCaller
          { registers := (extractMessageRegisters decoded.msgRegs decoded.msgInfo).extract
              1 (extractMessageRegisters decoded.msgRegs decoded.msgInfo).size,
            caps := #[], badge := replyBadge }
          (determineExecutingCore st tid) st).1).objects[s.toObjId]?
        = some (.tcb sTcb) →
      sTcb.schedContextBinding ≠ .donated sc0 prevCaller) ∧
    (∃ tcb : TCB,
      ((endpointReplyOnCore tid prevCaller
          { registers := (extractMessageRegisters decoded.msgRegs decoded.msgInfo).extract
              1 (extractMessageRegisters decoded.msgRegs decoded.msgInfo).size,
            caps := #[], badge := replyBadge }
          (determineExecutingCore st tid) st).1).getTcb? tid = some tcb ∧
      tcb.ipcState = .ready) ∧
    allTimeoutBudgetsNone (endpointReplyOnCore tid prevCaller
      { registers := (extractMessageRegisters decoded.msgRegs decoded.msgInfo).extract
          1 (extractMessageRegisters decoded.msgRegs decoded.msgInfo).size,
        caps := #[], badge := replyBadge }
      (determineExecutingCore st tid) st).1 ∧
    replyIdEstablishFresh (endpointReplyOnCore tid prevCaller
      { registers := (extractMessageRegisters decoded.msgRegs decoded.msgInfo).extract
          1 (extractMessageRegisters decoded.msgRegs decoded.msgInfo).size,
        caps := #[], badge := replyBadge }
      (determineExecutingCore st tid) st).1 rid ∧
    (∀ (tcb : TCB),
      (endpointReceiveDualOnCore epId tid (some rid) (determineExecutingCore st tid)
          (endpointReplyOnCore tid prevCaller
            { registers := (extractMessageRegisters decoded.msgRegs decoded.msgInfo).extract
                1 (extractMessageRegisters decoded.msgRegs decoded.msgInfo).size,
              caps := #[], badge := replyBadge }
            (determineExecutingCore st tid) st).1).1.getTcb? tid = some tcb →
      ∀ m, tcb.pendingMessage = some m →
      ∀ (i : Nat) (c : TransferCap), m.caps[i]? = some c →
        ∀ b, c.cap.badge = some b → b.valid) ∧
    (∀ (nextThread : SeLe4n.ThreadId) (summary2 : CapTransferSummary)
        (sgi2 : Option (CoreId × Concurrency.SgiKind)) (st2 : SystemState),
      endpointReceiveDualWithCapsOnCore epId tid (some rid) gate.cspaceRoot
          decoded.capRecvSlot (determineExecutingCore st tid)
          (endpointReplyOnCore tid prevCaller
            { registers := (extractMessageRegisters decoded.msgRegs decoded.msgInfo).extract
                1 (extractMessageRegisters decoded.msgRegs decoded.msgInfo).size,
              caps := #[], badge := replyBadge }
            (determineExecutingCore st tid) st).1
        = (st2, .ok (nextThread, summary2, sgi2)) →
      st2.objects.invExt ∧
      (∀ tcb, st2.getTcb? ((recordedReplyServer? st prevCaller).getD tid) = some tcb →
        passiveServerIdleAllowed tcb.ipcState) ∧
      (∀ (tid' : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
        st2.getTcb? tid' = some tcb → tcb.schedContextBinding ≠ .donated scId tid) ∧
      (∀ st3, replyRecvReturnDonation tid ((recordedReplyServer? st prevCaller).getD tid)
          nextThread (determineExecutingCore st ((recordedReplyServer? st prevCaller).getD tid))
          st2 = .ok ((), st3) →
        st3.objects.invExt))

  /-- WS-RR RR4.14 — **stated confinement**: the answered caller carries no
      pending fault.  Since RR4 the `.reply` arm is seL4's `doReplyTransfer`,
      which branches on the answered thread's `tcbFault`; the fault branch has
      its own bundle theorem (`faultReplyOnCore_preserves_ipcInvariantFull`,
      `IPC/Invariant/FaultPreservation.lean`) but composing it here needs a
      lemma the reply chain does not yet carry — that the cross-core reply
      leaves its target `.ready`, hence `passiveServerIdleAllowed`, which is
      what the fault reply's abandon arm consumes at the *post*-state.  Rather
      than thread a post-state hypothesis (which the RR3 de-threading gate
      forbids) or leave the branch silently uncovered, the payoff is confined
      here and the composition is registered as debt in
      `docs/WORKSTREAM_HISTORY.md`.  It is a pre-state fact, so a caller
      discharges it before the step. -/
  replyNoPendingFault : ∀ rid (r : Reply) (callerTid : SeLe4n.ThreadId),
    decoded.syscallId = .reply → cap.target = .replyCap rid →
    st.getReply? rid = some r → r.caller = some callerTid →
    threadHasPendingFault st callerTid = false

/-- WS-RR RR3.24 (**the dispatch payoff**): every syscall `dispatchWithCap`
routes preserves `ipcInvariantFull`.  The capability-only tier delegates to
RR3.23's payoff; the IPC arms compose the per-transition bundles with the
staging writes.  Staged because the `.call` arm reads the staged call-chain
bundle; every hypothesis is a pre-state fact. -/
theorem dispatchWithCap_preserves_ipcInvariantFull
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (st st' : SystemState)
    (hPack : syscallDispatchQuiescence decoded tid gate cap st)
    (hStep : dispatchWithCap decoded tid gate cap st = .ok ((), st')) :
    ipcInvariantFull st' := by
  have hInv := hPack.reachable.ipcInvariantFull
  have hObjInv := hPack.reachable.objects_invExt
  have hBudgets := hPack.reachable.allTimeoutBudgetsNone
  unfold dispatchWithCap at hStep
  cases hCapOnly : dispatchCapabilityOnly decoded cap tid with
  | some k =>
      rw [hCapOnly] at hStep
      exact dispatchCapabilityOnly_preserves_ipcInvariantFull decoded cap tid k st st'
        hCapOnly hObjInv hInv hPack.capOnly hStep
  | none =>
      rw [hCapOnly] at hStep
      cases hSy : decoded.syscallId <;> simp only [hSy] at hStep <;>
        first
          | (unfold dispatchCapabilityOnly at hCapOnly
             simp only [hSy] at hCapOnly)
          | skip
      case send =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object epId =>
          cases hRes : resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
              gate.capDepth (cap.rights.mem .grant) st with
          | mk resolvedCaps stR =>
              simp only [hRes] at hStep
              obtain ⟨hRO, hRS, hRB⟩ := resolveExtraCaps_shape gate.cspaceRoot
                (decodeExtraCapAddrs decoded) gate.capDepth (cap.rights.mem .grant) st
                hInv.badgeWellFormed.2
              rw [hRes] at hRO hRS hRB
              have hInvR : ipcInvariantFull stR :=
                ipcInvariantFull_of_objects_scheduler_eq hRO hRS hInv
              have hObjInvR : stR.objects.invExt := by rw [hRO]; exact hObjInv
              have hBudgetsR : allTimeoutBudgetsNone stR := by
                intro t tcb hT
                exact hBudgets t tcb (by rw [← hRO]; exact hT)
              obtain ⟨tcbC, hTC, hReadyC, hBoundC⟩ := hPack.callerShape
              have hTCR : stR.getTcb? tid = some tcbC :=
                (SystemState.getTcb?_eq_some_iff stR tid tcbC).mpr
                  (by rw [hRO]; exact (SystemState.getTcb?_eq_some_iff st tid tcbC).mp hTC)
              have hFreshR := readyThread_endpointQueueFresh stR tid tcbC
                hInvR.queueHeadBlockedConsistent hInvR.endpointQueueTailBlockedConsistent
                ((SystemState.getTcb?_eq_some_iff stR tid tcbC).mp hTCR) hReadyC
              have hTailR := sendTailCrossQueueFresh stR epId
                hInvR.dualQueueSystemInvariant hInvR.endpointQueueTailBlockedConsistent
              have hSendInv := endpointSendDualWithCapsOnCore_preserves_ipcInvariantFull
                epId tid { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, caps := resolvedCaps, badge := cap.badge, capsGranted := cap.rights.mem .grant }
                cap.rights gate.cspaceRoot decoded.capRecvSlot
                (determineExecutingCore stR tid) stR
                hInvR hObjInvR hBudgetsR hRB hFreshR hTailR
                (fun tcb hTcb => by
                  rw [hTCR] at hTcb
                  obtain rfl := Option.some.inj hTcb
                  exact readyThread_notBlockedOnReceive tcbC hReadyC)
                (fun tcb hTcb => by
                  rw [hTCR] at hTcb
                  obtain rfl := Option.some.inj hTcb
                  exact readyThread_notBlockedOnReply tcbC hReadyC)
                (fun tcb hTcb => by
                  rw [hTCR] at hTcb
                  obtain rfl := Option.some.inj hTcb
                  exact hBoundC)
              cases hSend : endpointSendDualWithCapsOnCore epId tid
                  { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, caps := resolvedCaps, badge := cap.badge, capsGranted := cap.rights.mem .grant }
                  cap.rights gate.cspaceRoot decoded.capRecvSlot
                  (determineExecutingCore stR tid) stR with
              | mk st1 res1 =>
                  rw [hSend] at hStep hSendInv
                  cases res1 with
                  | error e => simp only [] at hStep; cases hStep
                  | ok pair1 =>
                      obtain ⟨summary, sgi1⟩ := pair1
                      simp only [] at hStep
                      have hObjInv1 : st1.objects.invExt :=
                        hPack.sendStage epId hSy hTgt st1 _ (by rw [hRes]; exact hSend)
                      cases hClear : clearWokenReceiverStash
                          ((stR.getEndpoint? epId).bind (·.receiveQ.head)) st1 with
                      | error e => rw [hClear] at hStep; cases hStep
                      | ok pair2 =>
                          rw [hClear] at hStep
                          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                          have hClearInv := clearWokenReceiverStash_preserves_ipcInvariantFull
                            _ st1 pair2 hObjInv1 hSendInv hClear
                          have hClearObjInv : pair2.2.objects.invExt := by
                            unfold clearWokenReceiverStash at hClear
                            cases hW : (stR.getEndpoint? epId).bind (·.receiveQ.head) with
                            | none => rw [hW] at hClear; cases hClear; exact hObjInv1
                            | some receiver =>
                                rw [hW] at hClear
                                simp only [] at hClear
                                cases hTcb2 : st1.getTcb? receiver with
                                | none => rw [hTcb2] at hClear; cases hClear; exact hObjInv1
                                | some tcb2 =>
                                    rw [hTcb2] at hClear
                                    simp only [] at hClear
                                    split at hClear <;> cases hClear
                                    · exact RHTable_insert_preserves_invExt _ _ _ hObjInv1
                                    · exact hObjInv1
                          rw [← hStep]
                          exact stageWokenDelivery_preserves_ipcInvariantFull pair2.2 _ _
                            hClearObjInv hClearInv
        all_goals try cases hStep
      case receive =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object epId =>
          cases hRid : resolveRecvReplyId gate decoded st with
          | error e => simp only [hRid] at hStep; cases hStep
          | ok replyIdOpt =>
              simp only [hRid] at hStep
              obtain ⟨hRidFresh, hDeliveredBadges, hRecvInvExt⟩ :=
                hPack.recvStage epId replyIdOpt hSy hTgt hRid
              obtain ⟨tcbC, hTC, hReadyC, hBoundC⟩ := hPack.callerShape
              have hFresh := readyThread_endpointQueueFresh st tid tcbC
                hInv.queueHeadBlockedConsistent hInv.endpointQueueTailBlockedConsistent
                ((SystemState.getTcb?_eq_some_iff st tid tcbC).mp hTC) hReadyC
              have hTailR := recvTailCrossQueueFresh st epId
                hInv.dualQueueSystemInvariant hInv.endpointQueueTailBlockedConsistent
              have hRecvInv := endpointReceiveDualWithCapsOnCore_preserves_ipcInvariantFull
                epId tid replyIdOpt gate.cspaceRoot decoded.capRecvSlot
                (determineExecutingCore st tid) st hInv hObjInv hBudgets hFresh hTailR
                hRidFresh
                (fun tcb hTcb => by
                  rw [hTC] at hTcb
                  obtain rfl := Option.some.inj hTcb
                  exact readyThread_notBlockedOnReceive tcbC hReadyC)
                (fun tcb hTcb => by
                  rw [hTC] at hTcb
                  obtain rfl := Option.some.inj hTcb
                  exact hReadyC)
                hDeliveredBadges
              cases hRecv : endpointReceiveDualWithCapsOnCore epId tid replyIdOpt
                  gate.cspaceRoot decoded.capRecvSlot (determineExecutingCore st tid) st with
              | mk st1 res1 =>
                  rw [hRecv] at hStep hRecvInv
                  cases res1 with
                  | error e => simp only [] at hStep; cases hStep
                  | ok triple =>
                      obtain ⟨nextThread, summary, sgi1⟩ := triple
                      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                      have hObjInv1 : st1.objects.invExt :=
                        hRecvInvExt st1 _ hRecv
                      have hSC := stageWokenSendCompletion_preserves_ipcInvariantFull st1
                        ((st.getEndpoint? epId).bind (·.sendQ.head)) hObjInv1 hRecvInv
                      have hSCobj := stageWokenSendCompletion_objects_invExt st1
                        ((st.getEndpoint? epId).bind (·.sendQ.head)) hObjInv1
                      rw [← hStep]
                      exact stageDeliveredMessage_preserves_ipcInvariantFull _ tid _
                        hSCobj hSC
        all_goals try cases hStep
      case call =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object epId =>
          cases hRes : resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
              gate.capDepth (cap.rights.mem .grant) st with
          | mk resolvedCaps stR =>
              simp only [hRes] at hStep
              obtain ⟨hRO, hRS, hRB⟩ := resolveExtraCaps_shape gate.cspaceRoot
                (decodeExtraCapAddrs decoded) gate.capDepth (cap.rights.mem .grant) st
                hInv.badgeWellFormed.2
              rw [hRes] at hRO hRS hRB
              have hInvR : ipcInvariantFull stR :=
                ipcInvariantFull_of_objects_scheduler_eq hRO hRS hInv
              have hObjInvR : stR.objects.invExt := by rw [hRO]; exact hObjInv
              have hBudgetsR : allTimeoutBudgetsNone stR := by
                intro t tcb hT
                exact hBudgets t tcb (by rw [← hRO]; exact hT)
              obtain ⟨tcbC, hTC, hReadyC, hBoundC⟩ := hPack.callerShape
              have hTCR : stR.getTcb? tid = some tcbC :=
                (SystemState.getTcb?_eq_some_iff stR tid tcbC).mpr
                  (by rw [hRO]; exact (SystemState.getTcb?_eq_some_iff st tid tcbC).mp hTC)
              have hFreshR := readyThread_endpointQueueFresh stR tid tcbC
                hInvR.queueHeadBlockedConsistent hInvR.endpointQueueTailBlockedConsistent
                ((SystemState.getTcb?_eq_some_iff stR tid tcbC).mp hTCR) hReadyC
              have hTailR := sendTailCrossQueueFresh stR epId
                hInvR.dualQueueSystemInvariant hInvR.endpointQueueTailBlockedConsistent
              have hNeR : ∀ ep receiverTid, stR.getEndpoint? epId = some ep →
                  ep.receiveQ.head = some receiverTid → tid ≠ receiverTid := by
                intro ep receiverTid hEp hHead
                refine hPack.callNotSelfRendezvous epId hSy hTgt ep receiverTid ?_ hHead
                rw [show st.getEndpoint? epId = stR.getEndpoint? epId from by
                  unfold SystemState.getEndpoint?
                  rw [hRO]]
                exact hEp
              have hCallInv := endpointCallCrossCoreDispatch_preserves_ipcInvariantFull
                epId tid { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, caps := resolvedCaps, badge := cap.badge, capsGranted := cap.rights.mem .grant }
                cap.rights gate.cspaceRoot decoded.capRecvSlot
                (determineExecutingCore stR tid) stR
                hInvR hObjInvR hBudgetsR hRB hFreshR hTailR
                (fun tcb hTcb => by
                  rw [hTCR] at hTcb
                  obtain rfl := Option.some.inj hTcb
                  exact readyThread_notBlockedOnReceive tcbC hReadyC)
                (fun tcb hTcb => by
                  rw [hTCR] at hTcb
                  obtain rfl := Option.some.inj hTcb
                  exact hReadyC)
                (fun tcb hTcb => by
                  rw [hTCR] at hTcb
                  obtain rfl := Option.some.inj hTcb
                  exact readyThread_notBlockedOnReply tcbC hReadyC)
                (fun tcb hTcb => by
                  rw [hTCR] at hTcb
                  obtain rfl := Option.some.inj hTcb
                  exact hBoundC)
                hNeR
              cases hCall : endpointCallCrossCoreDispatch epId tid
                  { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, caps := resolvedCaps, badge := cap.badge, capsGranted := cap.rights.mem .grant }
                  cap.rights gate.cspaceRoot decoded.capRecvSlot
                  (determineExecutingCore stR tid) stR with
              | mk st1 res1 =>
                  rw [hCall] at hStep hCallInv
                  cases res1 with
                  | error e => simp only [] at hStep; cases hStep
                  | ok pair1 =>
                      obtain ⟨summary, sgi1⟩ := pair1
                      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                      have hObjInv1 : st1.objects.invExt :=
                        hPack.callStage epId hSy hTgt st1 _ (by rw [hRes]; exact hCall)
                      rw [← hStep]
                      exact stageWokenDelivery_preserves_ipcInvariantFull st1 _ _
                        hObjInv1 hCallInv
        all_goals try cases hStep
      case reply =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case replyCap rid =>
          cases hR : st.getReply? rid with
          | none => simp only [hR] at hStep; cases hStep
          | some reply =>
              simp only [hR] at hStep
              cases hCaller : reply.caller with
              | none => simp only [hCaller] at hStep; cases hStep
              | some callerTid =>
                  simp only [hCaller] at hStep
                  obtain ⟨hDon, hReplyInvExt⟩ :=
                    hPack.replyStage rid reply callerTid hSy hTgt hR hCaller
                  -- WS-RR RR4.14: the seam's ordinary branch, under the pack's
                  -- stated confinement.  On an unfaulted caller it is the
                  -- pre-RR4 body verbatim, so the rest of this proof is
                  -- unchanged.
                  rw [replyTransferOnCore_of_no_fault tid callerTid decoded.msgInfo
                    decoded.msgRegs _ _ st
                    (hPack.replyNoPendingFault rid reply callerTid hSy hTgt hR hCaller)] at hStep
                  have hReplyInv := endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull
                    tid callerTid
                    { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, caps := #[], badge := cap.badge }
                    (determineExecutingCore st tid) st hInv hObjInv
                    (fun expected hExp => (hDon expected hExp).1) hBudgets
                    (fun expected hExp => (hDon expected hExp).2)
                  cases hReply : endpointReplyCrossCoreDispatch tid callerTid
                      { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, caps := #[], badge := cap.badge }
                      (determineExecutingCore st tid) st with
                  | mk st1 res1 =>
                      rw [hReply] at hStep hReplyInv
                      cases res1 with
                      | error e => simp only [] at hStep; cases hStep
                      | ok u1 =>
                          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                          have hObjInv1 : st1.objects.invExt :=
                            hReplyInvExt st1 _ hReply
                          rw [← hStep]
                          exact stageDeliveredMessage_preserves_ipcInvariantFull st1
                            callerTid 0 hObjInv1 hReplyInv
        all_goals try cases hStep
      case cspaceMint =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object cnodeId =>
          cases hDec : decodeCSpaceMintArgs decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              refine cspaceMintWithCdt_preserves_ipcInvariantFull st st' _ _ args.rights _
                hObjInv hInv ?_ hStep
              intro b hb
              split at hb
              · cases hb
              · obtain rfl := Option.some.inj hb
                exact hPack.mintBadgeValid args hSy hDec
        all_goals try cases hStep
      case cspaceCopy =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object cnodeId =>
          cases hDec : decodeCSpaceCopyArgs decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              exact cspaceCopy_preserves_ipcInvariantFull st st' _ _ hObjInv hInv hStep
        all_goals try cases hStep
      case cspaceMove =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object cnodeId =>
          cases hDec : decodeCSpaceMoveArgs decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              exact cspaceMove_preserves_ipcInvariantFull st st' _ _ hObjInv hInv hStep
        all_goals try cases hStep
      case serviceRegister =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object epId =>
          cases hDec : decodeServiceRegisterArgs decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              exact registerService_preserves_ipcInvariantFull st st' _ hInv hStep
        all_goals try cases hStep
      case notificationSignal =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object notifId =>
          cases hDec : decodeNotificationSignalArgs decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              have hNoBound := hPack.signalNoBoundTarget notifId hSy hTgt
              have hReduce : notificationSignalBoundCrossCoreDispatch notifId args.badge
                  tid st = notificationSignalOnCore notifId args.badge
                    (determineExecutingCore st tid) st := by
                unfold notificationSignalBoundCrossCoreDispatch
                exact notificationSignalBoundOnCore_fallthrough_eq notifId args.badge
                  (determineExecutingCore st tid) st hNoBound
              rw [hReduce] at hStep
              have hSigInv := notificationSignalOnCore_preserves_ipcInvariantFull notifId
                args.badge (determineExecutingCore st tid) st hInv hObjInv
                hPack.reachable.notificationWaiterConsistent hBudgets
              cases hSig : notificationSignalOnCore notifId args.badge
                  (determineExecutingCore st tid) st with
              | mk st1 res1 =>
                  rw [hSig] at hStep hSigInv
                  cases res1 with
                  | error e => simp only [] at hStep; cases hStep
                  | ok u1 =>
                      simp only [] at hStep
                      have hObjInv1 : st1.objects.invExt := by
                        have h := notificationSignalOnCore_preserves_objects_invExt
                          notifId args.badge (determineExecutingCore st tid) st hObjInv
                        rw [hSig] at h; exact h
                      cases hClear : clearWokenReceiverStash
                          ((boundDeliveryTarget? st notifId).map (·.1)) st1 with
                      | error e => rw [hClear] at hStep; cases hStep
                      | ok pair2 =>
                          rw [hClear] at hStep
                          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                          have hClearInv := clearWokenReceiverStash_preserves_ipcInvariantFull
                            _ st1 pair2 hObjInv1 hSigInv hClear
                          have hClearObjInv : pair2.2.objects.invExt := by
                            unfold clearWokenReceiverStash at hClear
                            cases hW : (boundDeliveryTarget? st notifId).map (·.1) with
                            | none => rw [hW] at hClear; cases hClear; exact hObjInv1
                            | some receiver =>
                                rw [hW] at hClear
                                simp only [] at hClear
                                cases hTcb2 : st1.getTcb? receiver with
                                | none => rw [hTcb2] at hClear; cases hClear; exact hObjInv1
                                | some tcb2 =>
                                    rw [hTcb2] at hClear
                                    simp only [] at hClear
                                    split at hClear <;> cases hClear
                                    · exact RHTable_insert_preserves_invExt _ _ _ hObjInv1
                                    · exact hObjInv1
                          have hD1 := stageWokenDelivery_preserves_ipcInvariantFull pair2.2
                            ((boundDeliveryTarget? st notifId).map (·.1)) 0
                            hClearObjInv hClearInv
                          have hD1obj : (Architecture.stageWokenDelivery pair2.2
                              ((boundDeliveryTarget? st notifId).map (·.1)) 0).objects.invExt := by
                            cases hW : (boundDeliveryTarget? st notifId).map (·.1) with
                            | none => exact hClearObjInv
                            | some w =>
                                rw [Architecture.stageWokenDelivery_some]
                                exact stageDeliveredMessage_objects_invExt pair2.2 w 0
                                  hClearObjInv
                          rw [← hStep]
                          exact stageWokenDelivery_preserves_ipcInvariantFull _ _ 0
                            hD1obj hD1
        all_goals try cases hStep
      case notificationWait =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object notifId =>
          obtain ⟨tcbC, hTC, hReadyC, hBoundC⟩ := hPack.callerShape
          have hWaitInv := notificationWaitCrossCoreDispatch_preserves_ipcInvariantFull
            notifId tid st hInv hObjInv
            (fun tcb hTcb => by
              rw [hTC] at hTcb
              obtain rfl := Option.some.inj hTcb
              exact readyThread_notBlockedOnReceive tcbC hReadyC)
            (fun tcb hTcb => by
              rw [hTC] at hTcb
              obtain rfl := Option.some.inj hTcb
              exact readyThread_notBlockedOnReply tcbC hReadyC)
            hBudgets
            (fun tcb hTcb => by
              rw [hTC] at hTcb
              obtain rfl := Option.some.inj hTcb
              exact hReadyC)
          cases hWait : notificationWaitCrossCoreDispatch notifId tid st with
          | mk st1 res1 =>
              rw [hWait] at hStep hWaitInv
              cases res1 with
              | error e => simp only [] at hStep; cases hStep
              | ok badge? =>
                  cases badge? with
                  | none =>
                      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                      rw [← hStep]
                      exact hWaitInv
                  | some badge =>
                      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                      have hObjInv1 : st1.objects.invExt := by
                        have h := notificationWaitCrossCoreDispatch_preserves_objects_invExt
                          notifId tid st hObjInv
                        rw [hWait] at h; exact h
                      rw [← hStep]
                      exact writeReturnFrameToTcb_preserves_ipcInvariantFull st1 tid _
                        hObjInv1 hWaitInv
        all_goals try cases hStep
      case replyRecv =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object epId =>
          cases hRR : resolveReplyRecvReply gate decoded st with
          | error e => simp only [hRR] at hStep; cases hStep
          | ok triple =>
              obtain ⟨rid, prevCaller, replyBadge⟩ := triple
              simp only [hRR] at hStep
              obtain ⟨hNoEdge1, hReady1, hBudgets1, hRidFresh1, hBadges1, hRetStage⟩ :=
                hPack.replyRecvStage rid prevCaller replyBadge epId hSy hTgt hRR
              cases hBody : replyRecvBody epId tid rid prevCaller
                  { registers := (extractMessageRegisters decoded.msgRegs decoded.msgInfo).extract 1 (extractMessageRegisters decoded.msgRegs decoded.msgInfo).size, caps := #[], badge := replyBadge }
                  gate.cspaceRoot decoded.capRecvSlot (determineExecutingCore st tid) st with
              | error e => simp only [hBody] at hStep; cases hStep
              | ok pairB =>
                  obtain ⟨summary, stB⟩ := pairB
                  simp only [hBody] at hStep
                  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                  obtain ⟨hInvB, hObjInvB⟩ := replyRecvBody_preserves_ipcInvariantFull
                    epId tid rid prevCaller _ gate.cspaceRoot decoded.capRecvSlot
                    (determineExecutingCore st tid) st stB summary
                    hPack.reachable hNoEdge1 hReady1 hBudgets1 hRidFresh1 hBadges1
                    hRetStage hBody
                  rw [← hStep]
                  exact stageDeliveredMessage_preserves_ipcInvariantFull stB tid _
                    hObjInvB hInvB
        all_goals try cases hStep
      all_goals cases hStep

-- ============================================================================
-- §5  The `dispatchSyscall` payoff
-- ============================================================================

/-- WS-RR RR3.25 (**the syscall-entry payoff**): `dispatchSyscall` preserves
`ipcInvariantFull` — the capability resolution is read-only, the dispatch tier
is RR3.24's payoff, and the taint application writes only the taint map. -/
theorem dispatchSyscall_preserves_ipcInvariantFull
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hPack : ∀ (gate : SyscallGate) (cap : Capability),
      syscallLookupCap gate st = .ok (cap, st) →
      syscallDispatchQuiescence decoded tid gate cap st)
    (hStep : dispatchSyscall decoded tid st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold dispatchSyscall at hStep
  cases hT : st.objects[tid.toObjId]? with
  | none => simp only [hT] at hStep; cases hStep
  | some obj =>
      cases obj with
      | tcb tcb =>
          simp only [hT] at hStep
          cases hRoot : st.objects[tcb.cspaceRoot]? with
          | none => simp only [hRoot] at hStep; cases hStep
          | some rootObj =>
              cases rootObj with
              | cnode rootCn =>
                  simp only [hRoot] at hStep
                  cases hInvk : syscallInvoke { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr, capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId } (dispatchWithCap decoded tid { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr, capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }) st with
                  | error e => rw [hInvk] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨u, stPost⟩ := pair; cases u
                      rw [hInvk] at hStep
                      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                      unfold syscallInvoke at hInvk
                      cases hLk : syscallLookupCap { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr, capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId } st with
                      | error e => rw [hLk] at hInvk; cases hInvk
                      | ok pairL =>
                          obtain ⟨cap, stL⟩ := pairL
                          rw [hLk] at hInvk
                          obtain ⟨-, -, -, hStEq⟩ :=
                            syscallResolveCap_implies_capability_at_slot _ st cap stL
                              (syscallResolveCap_of_lookup _ st cap stL hLk)
                          subst hStEq
                          have hInvPost := dispatchWithCap_preserves_ipcInvariantFull
                            decoded tid _ cap stL stPost
                            (hPack _ cap hLk) hInvk
                          rw [← hStep]
                          refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hInvPost
                          · exact applySyscallTaint_objects _ _ _
                          · exact applySyscallTaint_scheduler _ _ _
              | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
              | schedContext _ | reply _ => simp only [hRoot] at hStep; cases hStep
      | cnode _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
      | schedContext _ | reply _ => simp only [hT] at hStep; cases hStep


/-! ## §6  The flow-checked dispatch tier (WS-RR RR3.22, third item)

`dispatchWithCapChecked` mirrors `dispatchWithCap` arm for arm: the
capability tier is *shared* (both dispatchers match `dispatchCapabilityOnly`
first), every mirrored IPC arm wraps the same plumbing around a checked
transition whose wrapper is an if-tower over the unchecked one, and four
SM9 arms (`.declassify`, `.declassifySignal`, `.auditRead`, `.auditDrain`)
are live here while the unchecked dispatcher refuses them by design.

The payoff below does not re-prove the mirrored arms: in each one a
successful checked dispatch is shown to *be* a successful unchecked
dispatch — the flow gates only filter — so the theorem consumes
`dispatchWithCap_preserves_ipcInvariantFull` through the rebuilt unchecked
dispatch equation, turning every "mirrors the unchecked arm" comment in
`Kernel/API.lean` into a machine-checked fact.  The SM9 arms close from
their transitions' own frames (`auditReadFromCore_frame` pins `st' = st`;
`auditDrain_frame` and `declassifyObjectFromCore_frame_of_ok` pin an
audit-log-only rewrite, which no `ipcInvariantFull` conjunct reads) plus
the declassified signal's fallthrough bundle, under the same
unbound-delivery confinement as the ordinary signal arm (bound delivery is
SM6.D's registered debt on both tiers). -/

/-- Pre-state pack for the flow-checked dispatch tier: the unchecked pack,
plus the declassifying signal's unbound-delivery confinement — that arm is
live only on this tier, so only this tier's pack carries its confinement.
Every field is a pre-state fact. -/
structure checkedSyscallDispatchQuiescence (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState) : Prop where
  base : syscallDispatchQuiescence decoded tid gate cap st
  declassifySignalNoBoundTarget : ∀ notifId,
    decoded.syscallId = .declassifySignal → cap.target = .object notifId →
    boundDeliveryTarget? st notifId = none

/-- The flow-checked dispatch tier preserves `ipcInvariantFull`.  Mirrored
arms reduce to `dispatchWithCap_preserves_ipcInvariantFull` through the
rebuilt unchecked dispatch equation; the four SM9 arms close from their
transitions' frames and the declassified signal's fallthrough bundle. -/
theorem dispatchWithCapChecked_preserves_ipcInvariantFull
    (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (gate : SyscallGate) (cap : Capability)
    (st st' : SystemState)
    (hQ : checkedSyscallDispatchQuiescence decoded tid gate cap st)
    (hStep : dispatchWithCapChecked ctx decoded tid gate cap st = .ok ((), st')) :
    ipcInvariantFull st' := by
  have hInv := hQ.base.reachable.ipcInvariantFull
  have hObjInv := hQ.base.reachable.objects_invExt
  unfold dispatchWithCapChecked at hStep
  cases hCapOnly : dispatchCapabilityOnly decoded cap tid with
  | some k =>
      rw [hCapOnly] at hStep
      exact dispatchCapabilityOnly_preserves_ipcInvariantFull decoded cap tid k st st'
        hCapOnly hObjInv hInv hQ.base.capOnly hStep
  | none =>
      rw [hCapOnly] at hStep
      have hCapOnly0 := hCapOnly
      cases hSy : decoded.syscallId <;> simp only [hSy] at hStep <;>
        first
          | (unfold dispatchCapabilityOnly at hCapOnly
             simp only [hSy] at hCapOnly)
          | skip
      case send =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object epId =>
          cases hRes : resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
              gate.capDepth (cap.rights.mem .grant) st with
          | mk resolvedCaps stR =>
              simp only [hRes] at hStep
              cases hDisp : endpointSendCrossCoreDispatchChecked ctx epId tid
                  { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
                    caps := resolvedCaps, badge := cap.badge,
                    capsGranted := cap.rights.mem .grant } cap.rights gate.cspaceRoot
                  decoded.capRecvSlot (determineExecutingCore stR tid) stR with
              | mk st1 res1 =>
                  rw [hDisp] at hStep
                  unfold endpointSendCrossCoreDispatchChecked at hDisp
                  split at hDisp
                  · injection hDisp with hA hB
                    subst hB
                    simp only [] at hStep; cases hStep
                  split at hDisp
                  · injection hDisp with hA hB
                    subst hB
                    simp only [] at hStep; cases hStep
                  split at hDisp
                  · have hU : dispatchWithCap decoded tid gate cap st
                        = .ok ((), st') := by
                      unfold dispatchWithCap
                      simp only [hCapOnly0, hSy, hTgt, hRes, hDisp]
                      exact hStep
                    exact dispatchWithCap_preserves_ipcInvariantFull decoded tid gate
                      cap st st' hQ.base hU
                  · injection hDisp with hA hB
                    subst hB
                    simp only [] at hStep; cases hStep
        all_goals cases hStep
      case receive =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object epId =>
          split at hStep
          · cases hStep
          · have hU : dispatchWithCap decoded tid gate cap st = .ok ((), st') := by
              unfold dispatchWithCap
              simp only [hCapOnly0, hSy, hTgt]
              exact hStep
            exact dispatchWithCap_preserves_ipcInvariantFull decoded tid gate cap st st'
              hQ.base hU
        all_goals cases hStep
      case call =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object epId =>
          cases hRes : resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
              gate.capDepth (cap.rights.mem .grant) st with
          | mk resolvedCaps stR =>
              simp only [hRes] at hStep
              cases hDisp : endpointCallCrossCoreDispatchChecked ctx epId tid
                  { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
                    caps := resolvedCaps, badge := cap.badge,
                    capsGranted := cap.rights.mem .grant } cap.rights gate.cspaceRoot
                  decoded.capRecvSlot (determineExecutingCore stR tid) stR with
              | mk st1 res1 =>
                  rw [hDisp] at hStep
                  unfold endpointCallCrossCoreDispatchChecked at hDisp
                  split at hDisp
                  · have hU : dispatchWithCap decoded tid gate cap st
                        = .ok ((), st') := by
                      unfold dispatchWithCap
                      simp only [hCapOnly0, hSy, hTgt, hRes, hDisp]
                      exact hStep
                    exact dispatchWithCap_preserves_ipcInvariantFull decoded tid gate
                      cap st st' hQ.base hU
                  · injection hDisp with hA hB
                    subst hB
                    simp only [] at hStep; cases hStep
        all_goals cases hStep
      case reply =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case replyCap rid =>
          cases hRep : st.getReply? rid with
          | none => simp only [hRep] at hStep; cases hStep
          | some reply =>
              simp only [hRep] at hStep
              cases hCaller : reply.caller with
              | none => simp only [hCaller] at hStep; cases hStep
              | some callerTid =>
                  simp only [hCaller] at hStep
                  split at hStep
                  next hFlow =>
                    -- WS-RR RR4.14: the reply seam collapses checked → unchecked
                    -- on *both* branches under the arm's own flow guard.
                    rw [replyTransferOnCoreChecked_eq_unchecked_of_flow_allowed ctx tid
                          callerTid decoded.msgInfo decoded.msgRegs _
                          (determineExecutingCore st tid) st hFlow] at hStep
                    have hU : dispatchWithCap decoded tid gate cap st
                        = .ok ((), st') := by
                      unfold dispatchWithCap
                      simp only [hCapOnly0, hSy, hTgt, hRep, hCaller]
                      exact hStep
                    exact dispatchWithCap_preserves_ipcInvariantFull decoded tid gate
                      cap st st' hQ.base hU
                  next => cases hStep
        all_goals cases hStep
      case cspaceMint =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object cnodeId =>
          cases hDec : decodeCSpaceMintArgs decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              unfold cspaceMintChecked at hStep
              simp only [] at hStep
              split at hStep
              · have hU : dispatchWithCap decoded tid gate cap st = .ok ((), st') := by
                  unfold dispatchWithCap
                  simp only [hCapOnly0, hSy, hTgt, hDec]
                  exact hStep
                exact dispatchWithCap_preserves_ipcInvariantFull decoded tid gate cap
                  st st' hQ.base hU
              · cases hStep
        all_goals cases hStep
      case cspaceCopy =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object cnodeId =>
          cases hDec : decodeCSpaceCopyArgs decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              unfold cspaceCopyChecked at hStep
              simp only [] at hStep
              split at hStep
              · have hU : dispatchWithCap decoded tid gate cap st = .ok ((), st') := by
                  unfold dispatchWithCap
                  simp only [hCapOnly0, hSy, hTgt, hDec]
                  exact hStep
                exact dispatchWithCap_preserves_ipcInvariantFull decoded tid gate cap
                  st st' hQ.base hU
              · cases hStep
        all_goals cases hStep
      case cspaceMove =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object cnodeId =>
          cases hDec : decodeCSpaceMoveArgs decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              unfold cspaceMoveChecked at hStep
              simp only [] at hStep
              split at hStep
              · have hU : dispatchWithCap decoded tid gate cap st = .ok ((), st') := by
                  unfold dispatchWithCap
                  simp only [hCapOnly0, hSy, hTgt, hDec]
                  exact hStep
                exact dispatchWithCap_preserves_ipcInvariantFull decoded tid gate cap
                  st st' hQ.base hU
              · cases hStep
        all_goals cases hStep
      case serviceRegister =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object epId =>
          cases hDec : decodeServiceRegisterArgs decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              unfold registerServiceChecked at hStep
              simp only [] at hStep
              split at hStep
              · have hU : dispatchWithCap decoded tid gate cap st = .ok ((), st') := by
                  unfold dispatchWithCap
                  simp only [hCapOnly0, hSy, hTgt, hDec]
                  exact hStep
                exact dispatchWithCap_preserves_ipcInvariantFull decoded tid gate cap
                  st st' hQ.base hU
              · cases hStep
        all_goals cases hStep
      case notificationSignal =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object notifId =>
          cases hDec : decodeNotificationSignalArgs decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              have hNoBound := hQ.base.signalNoBoundTarget notifId hSy hTgt
              cases hFlow : securityFlowsTo (ctx.threadLabelOf tid)
                  (ctx.objectLabelOf notifId) with
              | false =>
                  rw [notificationSignalBoundCrossCoreDispatchChecked_flow_denied
                        ctx notifId tid args.badge st hFlow] at hStep
                  simp only [] at hStep; cases hStep
              | true =>
                  rw [notificationSignalBoundCrossCoreDispatchChecked_flow_allowed_no_delivery
                        ctx notifId tid args.badge st hFlow hNoBound] at hStep
                  have hU : dispatchWithCap decoded tid gate cap st = .ok ((), st') := by
                    unfold dispatchWithCap
                    simp only [hCapOnly0, hSy, hTgt, hDec]
                    exact hStep
                  exact dispatchWithCap_preserves_ipcInvariantFull decoded tid gate
                    cap st st' hQ.base hU
        all_goals cases hStep
      case notificationWait =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object notifId =>
          cases hFlow : securityFlowsTo (ctx.objectLabelOf notifId)
              (ctx.threadLabelOf tid) with
          | false =>
              rw [notificationWaitCrossCoreDispatchChecked_flow_denied
                    ctx notifId tid st hFlow] at hStep
              simp only [] at hStep; cases hStep
          | true =>
              rw [notificationWaitCrossCoreDispatchChecked_flow_allowed
                    ctx notifId tid st hFlow] at hStep
              have hU : dispatchWithCap decoded tid gate cap st = .ok ((), st') := by
                unfold dispatchWithCap
                simp only [hCapOnly0, hSy, hTgt]
                exact hStep
              exact dispatchWithCap_preserves_ipcInvariantFull decoded tid gate cap
                st st' hQ.base hU
        all_goals cases hStep
      case replyRecv =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object epId =>
          split at hStep
          · cases hStep
          · cases hResv : resolveReplyRecvReply gate decoded st with
            | error e => simp only [hResv] at hStep; cases hStep
            | ok trip =>
                obtain ⟨rid, prevCaller, replyBadge⟩ := trip
                simp only [hResv] at hStep
                split at hStep
                next hFlow =>
                  have hU : dispatchWithCap decoded tid gate cap st = .ok ((), st') := by
                    unfold dispatchWithCap
                    simp only [hCapOnly0, hSy, hTgt, hResv]
                    exact hStep
                  exact dispatchWithCap_preserves_ipcInvariantFull decoded tid gate cap
                    st st' hQ.base hU
                next => cases hStep
        all_goals cases hStep
      case declassify =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object targetId =>
          obtain ⟨tidC, hCur, hEq⟩ := declassifyObjectFromCore_frame_of_ok
            (liftLegacyContext ctx) ctx.declassificationPolicy
            (determineExecutingCore st tid) targetId st st' hStep
          rw [hEq]
          refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hInv
          · rfl
          · rfl
        all_goals cases hStep
      case declassifySignal =>
        cases hTgt : cap.target <;> simp only [hTgt] at hStep
        case object notifId =>
          cases hDec : decodeNotificationSignalArgs decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              have hNoBound := hQ.declassifySignalNoBoundTarget notifId hSy hTgt
              cases hDisp : notificationSignalDeclassifiedCrossCoreDispatch
                  (liftLegacyContext ctx) ctx.declassificationPolicy notifId tid
                  args.badge st with
              | mk st1 res1 =>
                  rw [hDisp] at hStep
                  cases res1 with
                  | error e => simp only [] at hStep; cases hStep
                  | ok sgi1 =>
                      simp only [] at hStep
                      rw [notificationSignalDeclassifiedCrossCoreDispatch_eq] at hDisp
                      have hSigInv : ipcInvariantFull st1 :=
                        notificationSignalDeclassifiedOnCore_preserves_ipcInvariantFull_fallthrough
                          (liftLegacyContext ctx) ctx.declassificationPolicy notifId
                          args.badge (determineExecutingCore st tid) st st1 sgi1 hNoBound
                          hInv hObjInv hQ.base.reachable.notificationWaiterConsistent
                          hQ.base.reachable.allTimeoutBudgetsNone hDisp
                      have hObjInv1 : st1.objects.invExt :=
                        notificationSignalDeclassifiedOnCore_preserves_objects_invExt
                          (liftLegacyContext ctx) ctx.declassificationPolicy notifId
                          args.badge (determineExecutingCore st tid) st st1 sgi1
                          hObjInv hDisp
                      cases hClear : clearWokenReceiverStash
                          ((boundDeliveryTarget? st notifId).map (·.1)) st1 with
                      | error e => rw [hClear] at hStep; cases hStep
                      | ok pair2 =>
                          rw [hClear] at hStep
                          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                          have hClearInv := clearWokenReceiverStash_preserves_ipcInvariantFull
                            _ st1 pair2 hObjInv1 hSigInv hClear
                          have hClearObjInv : pair2.2.objects.invExt := by
                            unfold clearWokenReceiverStash at hClear
                            cases hW : (boundDeliveryTarget? st notifId).map (·.1) with
                            | none => rw [hW] at hClear; cases hClear; exact hObjInv1
                            | some receiver =>
                                rw [hW] at hClear
                                simp only [] at hClear
                                cases hTcb2 : st1.getTcb? receiver with
                                | none => rw [hTcb2] at hClear; cases hClear; exact hObjInv1
                                | some tcb2 =>
                                    rw [hTcb2] at hClear
                                    simp only [] at hClear
                                    split at hClear <;> cases hClear
                                    · exact RHTable_insert_preserves_invExt _ _ _ hObjInv1
                                    · exact hObjInv1
                          have hD1 := stageWokenDelivery_preserves_ipcInvariantFull pair2.2
                            ((boundDeliveryTarget? st notifId).map (·.1)) 0
                            hClearObjInv hClearInv
                          have hD1obj : (Architecture.stageWokenDelivery pair2.2
                              ((boundDeliveryTarget? st notifId).map (·.1)) 0).objects.invExt := by
                            cases hW : (boundDeliveryTarget? st notifId).map (·.1) with
                            | none => exact hClearObjInv
                            | some w =>
                                rw [Architecture.stageWokenDelivery_some]
                                exact stageDeliveredMessage_objects_invExt pair2.2 w 0
                                  hClearObjInv
                          rw [← hStep]
                          exact stageWokenDelivery_preserves_ipcInvariantFull _ _ 0
                            hD1obj hD1
        all_goals cases hStep
      case auditRead =>
        cases hAuth : extractAuditAuthority cap with
        | error e => simp only [hAuth] at hStep; cases hStep
        | ok u =>
            simp only [hAuth] at hStep
            split at hStep
            case isTrue =>
              cases hDecA : decodeAuditReadArgs decoded with
              | error e => simp only [hDecA] at hStep; cases hStep
              | ok args =>
                  simp only [hDecA] at hStep
                  cases hOp : decodeAuditReadOp args.opcode args.index args.chunk with
                  | none => simp only [hOp] at hStep; cases hStep
                  | some op =>
                      simp only [hOp] at hStep
                      cases hRead : auditReadFromCore (liftLegacyContext ctx)
                          (validatedAuditMonitorClearance ctx)
                          (determineExecutingCore st tid) op st with
                      | error e => rw [hRead] at hStep; cases hStep
                      | ok pairR =>
                          obtain ⟨w, st1⟩ := pairR
                          rw [hRead] at hStep
                          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                          have hFr := auditReadFromCore_frame (liftLegacyContext ctx)
                            (validatedAuditMonitorClearance ctx)
                            (determineExecutingCore st tid) op st w st1 hRead
                          rw [← hStep, hFr]
                          exact writeReturnFrameToTcb_preserves_ipcInvariantFull st tid _
                            hObjInv hInv
            case isFalse => cases hStep
      case auditDrain =>
        cases hAuth : extractAuditAuthority cap with
        | error e => simp only [hAuth] at hStep; cases hStep
        | ok u =>
            simp only [hAuth] at hStep
            split at hStep
            case isTrue =>
              cases hDecA : decodeAuditDrainArgs decoded with
              | error e => simp only [hDecA] at hStep; cases hStep
              | ok args =>
                  simp only [hDecA] at hStep
                  cases hDrain : auditDrainVisiblePrefix (liftLegacyContext ctx)
                      (validatedAuditMonitorClearance ctx)
                      (determineExecutingCore st tid) args.count st with
                  | error e => rw [hDrain] at hStep; cases hStep
                  | ok pairD =>
                      obtain ⟨n, st1⟩ := pairD
                      rw [hDrain] at hStep
                      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                      obtain ⟨hEq, -, -⟩ := auditDrain_frame (liftLegacyContext ctx)
                        (validatedAuditMonitorClearance ctx)
                        (determineExecutingCore st tid) args.count st n st1 hDrain
                      have hInv1 : ipcInvariantFull st1 := by
                        rw [hEq]
                        refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hInv
                        · rfl
                        · rfl
                      have hObjInv1 : st1.objects.invExt := by
                        rw [hEq]; exact hObjInv
                      rw [← hStep]
                      exact writeReturnFrameToTcb_preserves_ipcInvariantFull st1 tid _
                        hObjInv1 hInv1
            case isFalse => cases hStep
      all_goals cases hStep


/-- The checked top-level dispatcher preserves `ipcInvariantFull`.  Mirrors
`dispatchSyscall_preserves_ipcInvariantFull` with two checked-tier
differences: the audit pair routes through the resolve-only lookup
(`syscallChecksTargetFirst` → `syscallInvokeResolved`), and the pack is
conditioned on `syscallResolveCap` — which every successful rights-gated
lookup implies (`syscallResolveCap_of_lookup`), so the one hypothesis
covers both routes. -/
theorem dispatchSyscallChecked_preserves_ipcInvariantFull
    (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hPack : ∀ (gate : SyscallGate) (cap : Capability),
      syscallResolveCap gate st = .ok (cap, st) →
      checkedSyscallDispatchQuiescence decoded tid gate cap st)
    (hStep : dispatchSyscallChecked ctx decoded tid st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold dispatchSyscallChecked at hStep
  cases hT : st.objects[tid.toObjId]? with
  | none => simp only [hT] at hStep; cases hStep
  | some obj =>
      cases obj with
      | tcb tcb =>
          simp only [hT] at hStep
          cases hRoot : st.objects[tcb.cspaceRoot]? with
          | none => simp only [hRoot] at hStep; cases hStep
          | some rootObj =>
              cases rootObj with
              | cnode rootCn =>
                  simp only [hRoot] at hStep
                  cases hTF : syscallChecksTargetFirst decoded.syscallId with
                  | true =>
                      simp only [hTF, if_true] at hStep
                      cases hInvk : syscallInvokeResolved { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr, capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId } (dispatchWithCapChecked ctx decoded tid { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr, capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }) st with
                      | error e => rw [hInvk] at hStep; cases hStep
                      | ok pair =>
                          obtain ⟨u, stPost⟩ := pair; cases u
                          rw [hInvk] at hStep
                          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                          unfold syscallInvokeResolved at hInvk
                          cases hRz : syscallResolveCap { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr, capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId } st with
                          | error e => rw [hRz] at hInvk; cases hInvk
                          | ok pairL =>
                              obtain ⟨cap, stL⟩ := pairL
                              rw [hRz] at hInvk
                              obtain ⟨-, -, -, hStEq⟩ :=
                                syscallResolveCap_implies_capability_at_slot _ st cap stL hRz
                              subst hStEq
                              have hInvPost := dispatchWithCapChecked_preserves_ipcInvariantFull
                                ctx decoded tid _ cap stL stPost (hPack _ cap hRz) hInvk
                              rw [← hStep]
                              refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hInvPost
                              · exact applySyscallTaint_objects _ _ _
                              · exact applySyscallTaint_scheduler _ _ _
                  | false =>
                      simp only [hTF, Bool.false_eq_true, if_false] at hStep
                      cases hInvk : syscallInvoke { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr, capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId } (dispatchWithCapChecked ctx decoded tid { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr, capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }) st with
                      | error e => rw [hInvk] at hStep; cases hStep
                      | ok pair =>
                          obtain ⟨u, stPost⟩ := pair; cases u
                          rw [hInvk] at hStep
                          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                          unfold syscallInvoke at hInvk
                          cases hLk : syscallLookupCap { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr, capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId } st with
                          | error e => rw [hLk] at hInvk; cases hInvk
                          | ok pairL =>
                              obtain ⟨cap, stL⟩ := pairL
                              rw [hLk] at hInvk
                              have hRz := syscallResolveCap_of_lookup _ st cap stL hLk
                              obtain ⟨-, -, -, hStEq⟩ :=
                                syscallResolveCap_implies_capability_at_slot _ st cap stL hRz
                              subst hStEq
                              have hInvPost := dispatchWithCapChecked_preserves_ipcInvariantFull
                                ctx decoded tid _ cap stL stPost (hPack _ cap hRz) hInvk
                              rw [← hStep]
                              refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hInvPost
                              · exact applySyscallTaint_objects _ _ _
                              · exact applySyscallTaint_scheduler _ _ _
              | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
              | schedContext _ | reply _ => simp only [hRoot] at hStep; cases hStep
      | cnode _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
      | schedContext _ | reply _ => simp only [hT] at hStep; cases hStep


/-! ## §7  The packs are inhabited (non-vacuity witnesses)

`ipcReachable` carries its own inhabitation witness (`ipcReachable_default`,
RR3.14) precisely because an unsatisfiable bundle makes every theorem taking
it vacuous.  The dispatch packs deserve the same pin, and their witness
cannot be the boot state: `callerShape` demands a ready, SchedContext-bound
caller, and a syscall genuinely has no caller before threads exist.

The witness below builds the smallest such state **through the per-arm
bundles themselves** — two retype writes carried by
`retypeWrite_preserves_ipcInvariantFull` (a fresh ready TCB, then a fresh
SchedContext) and the bind carried by
`ipcInvariantFull_of_schedBindingRewrite` — so the packs' first inhabitants
are also the retype and binding levers' first end-to-end consumers.  Every
conditional field is then discharged against a `.send`-shaped decode whose
capability targets a reply cap, which falsifies each arm-specific premise. -/

private def witnessTid : SeLe4n.ThreadId := ⟨1⟩
private def witnessScId : SeLe4n.SchedContextId := ⟨2⟩

private def witnessTcbFresh : TCB :=
  { tid := witnessTid, priority := ⟨0⟩, domain := ⟨0⟩, cspaceRoot := ⟨0⟩,
    vspaceRoot := ⟨0⟩, ipcBuffer := SeLe4n.VAddr.ofNat 0 }

private def witnessTcbBound : TCB :=
  { witnessTcbFresh with schedContextBinding := .bound witnessScId }

private def witnessScFresh : SeLe4n.Kernel.SchedContext :=
  { scId := witnessScId, budget := ⟨1⟩, period := ⟨1⟩, priority := ⟨0⟩,
    deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨1⟩ }

private def witnessScBound : SeLe4n.Kernel.SchedContext :=
  { witnessScFresh with boundThread := some witnessTid }

private def witnessSt1 : SystemState :=
  { (default : SystemState) with
    objects := (default : SystemState).objects.insert witnessTid.toObjId
      (.tcb witnessTcbFresh) }

private def witnessSt2 : SystemState :=
  { witnessSt1 with
    objects := witnessSt1.objects.insert witnessScId.toObjId
      (.schedContext witnessScFresh) }

private def witnessSt3 : SystemState :=
  { witnessSt2 with
    objects := (witnessSt2.objects.insert witnessTid.toObjId
        (.tcb witnessTcbBound)).insert witnessScId.toObjId
      (.schedContext witnessScBound) }

private theorem witnessKeysNe : witnessTid.toObjId ≠ witnessScId.toObjId := by
  decide

private theorem witnessObjInv0 : (default : SystemState).objects.invExt :=
  capabilityInvariantBundle.objectsInvExt
    (Architecture.default_system_state_proofLayerInvariantBundle).2.1

private theorem witnessObjInv1 : witnessSt1.objects.invExt :=
  RHTable_insert_preserves_invExt _ _ _ witnessObjInv0

private theorem witnessObjInv2 : witnessSt2.objects.invExt :=
  RHTable_insert_preserves_invExt _ _ _ witnessObjInv1

private theorem witnessObjInv3 : witnessSt3.objects.invExt :=
  RHTable_insert_preserves_invExt _ _ _
    (RHTable_insert_preserves_invExt _ _ _ witnessObjInv2)

private theorem witnessSt1_lookup (oid : SeLe4n.ObjId) :
    witnessSt1.objects[oid]?
      = if witnessTid.toObjId == oid then some (.tcb witnessTcbFresh) else none := by
  show (((default : SystemState).objects.insert witnessTid.toObjId
      (.tcb witnessTcbFresh)))[oid]? = _
  rw [RHTable_getElem?_eq_get?, RHTable_getElem?_insert _ _ _ witnessObjInv0]
  split
  · rfl
  · rw [← RHTable_getElem?_eq_get?, Architecture.default_objects_none]

private theorem witnessSt2_lookup (oid : SeLe4n.ObjId) :
    witnessSt2.objects[oid]?
      = if witnessScId.toObjId == oid then some (.schedContext witnessScFresh)
        else if witnessTid.toObjId == oid then some (.tcb witnessTcbFresh)
        else none := by
  show ((witnessSt1.objects.insert witnessScId.toObjId
      (.schedContext witnessScFresh)))[oid]? = _
  rw [RHTable_getElem?_eq_get?, RHTable_getElem?_insert _ _ _ witnessObjInv1]
  split
  · rfl
  · rw [← RHTable_getElem?_eq_get?, witnessSt1_lookup]

private theorem witnessSt3_lookup (oid : SeLe4n.ObjId) :
    witnessSt3.objects[oid]?
      = if witnessScId.toObjId == oid then some (.schedContext witnessScBound)
        else if witnessTid.toObjId == oid then some (.tcb witnessTcbBound)
        else none := by
  show (((witnessSt2.objects.insert witnessTid.toObjId
      (.tcb witnessTcbBound)).insert witnessScId.toObjId
        (.schedContext witnessScBound)))[oid]? = _
  rw [RHTable_getElem?_eq_get?,
    RHTable_getElem?_insert _ _ _ (RHTable_insert_preserves_invExt _ _ _ witnessObjInv2)]
  split
  · rfl
  · rw [RHTable_getElem?_insert _ _ _ witnessObjInv2]
    split
    · rfl
    · rw [← RHTable_getElem?_eq_get?, witnessSt2_lookup]
      split
      · next h1 => next h2 => exact absurd h1 (by simp_all)
      · rfl

/-- Nothing references any target in the empty boot store. -/
private theorem retypeTargetDetached_default (target : SeLe4n.ObjId) :
    retypeTargetDetached (default : SystemState) target := by
  constructor <;> (intros; simp_all [Architecture.default_objects_none])

/-- The fresh-TCB state references nothing at the SchedContext's slot: the
one stored thread is fully detached by construction. -/
private theorem witnessSt1_detached :
    retypeTargetDetached witnessSt1 witnessScId.toObjId := by
  constructor
  all_goals intros
  all_goals simp_all [witnessSt1_lookup]
  all_goals try simp_all [show witnessTid.toObjId ≠ witnessScId.toObjId from by decide]
  all_goals try obtain ⟨-, rfl⟩ := ‹_ ∧ _›
  all_goals simp_all [witnessTcbFresh]

private theorem witnessInv1 : ipcInvariantFull witnessSt1 := by
  refine retypeWrite_preserves_ipcInvariantFull (st := default)
    (target := witnessTid.toObjId) (newObj := .tcb witnessTcbFresh)
    ?_ ?_ rfl ?_ (retypeTargetDetached_default _) Architecture.default_ipcInvariantFull
  · rw [witnessSt1_lookup]; simp
  · intro oid hNe
    rw [witnessSt1_lookup, Architecture.default_objects_none]
    simp [show (witnessTid.toObjId == oid) = false from by
      simp [beq_eq_false_iff_ne]; exact fun h => hNe h.symm]
  · simp [witnessTcbFresh, retypeReplacementFresh]

private theorem witnessInv2 : ipcInvariantFull witnessSt2 := by
  refine retypeWrite_preserves_ipcInvariantFull (st := witnessSt1)
    (target := witnessScId.toObjId) (newObj := .schedContext witnessScFresh)
    ?_ ?_ rfl ?_ witnessSt1_detached witnessInv1
  · rw [witnessSt2_lookup]; simp
  · intro oid hNe
    rw [witnessSt2_lookup, witnessSt1_lookup]
    simp [show (witnessScId.toObjId == oid) = false from by
      simp [beq_eq_false_iff_ne]; exact fun h => hNe h.symm]
  · simp [retypeReplacementFresh]

private theorem witnessInv3 : ipcInvariantFull witnessSt3 := by
  refine ipcInvariantFull_of_schedBindingRewrite witnessSt2 witnessSt3 witnessTid
    witnessScId witnessTcbFresh witnessTcbBound witnessScFresh witnessScBound
    witnessInv2 ?_ ?_ ?_ ?_ ?_ rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_
  · rw [witnessSt2_lookup]
    simp [show (witnessScId.toObjId == witnessTid.toObjId) = false from by decide]
  · rw [witnessSt3_lookup]
    simp [show (witnessScId.toObjId == witnessTid.toObjId) = false from by decide]
  · rw [witnessSt2_lookup]; simp
  · rw [witnessSt3_lookup]; simp
  · intro oid hNeT hNeS
    rw [witnessSt3_lookup, witnessSt2_lookup]
    simp [show (witnessScId.toObjId == oid) = false from by
            simp [beq_eq_false_iff_ne]; exact fun h => hNeS h.symm,
          show (witnessTid.toObjId == oid) = false from by
            simp [beq_eq_false_iff_ne]; exact fun h => hNeT h.symm]
  · refine Or.inl ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro s sTcb sc0 hLk
      rw [witnessSt2_lookup] at hLk
      split at hLk
      · cases hLk
      · split at hLk
        · cases hLk
          simp [witnessTcbFresh]
        · cases hLk
    · intro t' tcb2 hNe hLk
      rw [witnessSt2_lookup] at hLk
      split at hLk
      · cases hLk
      · split at hLk
        · next h2 =>
            cases hLk
            exact absurd (SeLe4n.ThreadId.toObjId_injective _ _ (eq_of_beq h2)).symm hNe
        · cases hLk
  · refine ⟨?_⟩
    intro tid2 tcb' hLk hUnb _ _ _
    rw [witnessSt3_lookup] at hLk
    split at hLk
    · cases hLk
    · split at hLk
      · cases hLk
        simp [witnessTcbBound, witnessTcbFresh] at hUnb
      · cases hLk


private theorem witnessSt3_getTcb :
    witnessSt3.getTcb? witnessTid = some witnessTcbBound := by
  unfold SystemState.getTcb?
  rw [witnessSt3_lookup]
  simp [show (witnessScId.toObjId == witnessTid.toObjId) = false from by decide]

private theorem witnessReachable3 : ipcReachable witnessSt3 := by
  refine ⟨witnessInv3, witnessObjInv3, ?_, ?_, ?_⟩
  · intro tid tcb hLk
    rw [witnessSt3_lookup] at hLk
    split at hLk
    · cases hLk
    · split at hLk
      · cases hLk; rfl
      · cases hLk
  · intro tid tcb msg hLk hMsg
    rw [witnessSt3_lookup] at hLk
    split at hLk
    · cases hLk
    · split at hLk
      · cases hLk; cases hMsg
      · cases hLk
  · intro oid ntfn tid hLk _
    rw [witnessSt3_lookup] at hLk
    split at hLk
    · cases hLk
    · split at hLk
      · cases hLk
      · cases hLk

private def witnessDecoded : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := default, syscallId := .send }

private def witnessCap : Capability :=
  { target := .replyCap (SeLe4n.ReplyId.ofNat 0), rights := default }

private def witnessGate : SyscallGate :=
  { callerId := witnessTid, cspaceRoot := SeLe4n.ObjId.ofNat 0,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0,
    requiredRight := syscallRequiredRight .send }

private theorem witnessCapOnly :
    capabilityDispatchQuiescence witnessDecoded witnessCap witnessSt3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t tcb scId hLk hScId
    rw [witnessSt3_lookup] at hLk
    split at hLk
    · cases hLk
    · split at hLk
      · next hKey =>
          cases hLk
          simp [witnessTcbBound, witnessTcbFresh, SchedContextBinding.scId?] at hScId
          subst hScId
          have hT := SeLe4n.ThreadId.toObjId_injective _ _ (eq_of_beq hKey)
          subst hT
          refine ⟨witnessScBound, ?_, rfl⟩
          rw [witnessSt3_lookup]
          simp
      · cases hLk
  · intro c t tcb hLk hUnbound _
    rw [witnessSt3_lookup] at hLk
    split at hLk
    · cases hLk
    · split at hLk
      · cases hLk
        simp [witnessTcbBound, witnessTcbFresh] at hUnbound
      · cases hLk
  · intro args _ hDec
    simp only [decodeLifecycleRetypeArgs, witnessDecoded, requireMsgReg, bind,
      Except.bind] at hDec
    cases hDec
  · intro args _ hDec vThreadId hVal s sTcb sc0 hLk
    rw [witnessSt3_lookup] at hLk
    split at hLk
    · cases hLk
    · split at hLk
      · cases hLk
        simp [witnessTcbBound, witnessTcbFresh]
      · cases hLk
  · intro scObj _ hTgt
    simp [witnessCap] at hTgt
  · intro objId _ hTgt
    simp [witnessCap] at hTgt

/-- **The dispatch pack is inhabited.**  The witness state is built through
the per-arm bundles themselves — two `retypeWrite_preserves_ipcInvariantFull`
steps (a fresh ready TCB, then a fresh SchedContext) and one
`ipcInvariantFull_of_schedBindingRewrite` step (the bind) — so the packs'
first inhabitant is also those levers' first end-to-end consumer.  This
instance exercises the state-shaped fields; its `.send`-shaped decode and
`.replyCap` target leave the *indexed* fields vacuous, which is what the
per-arm instances in §7b below exist to close (PR #886 review). -/
theorem syscallDispatchQuiescence_inhabited :
    syscallDispatchQuiescence witnessDecoded witnessTid witnessGate witnessCap
      witnessSt3 := by
  refine ⟨witnessReachable3, witnessCapOnly,
    ⟨witnessTcbBound, witnessSt3_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp [witnessDecoded] at hSy
  · intro epId hSy hTgt
    simp [witnessCap] at hTgt
  · intro epId hSy
    simp [witnessDecoded] at hSy
  · intro epId hSy
    simp [witnessDecoded] at hSy
  · intro epId replyIdOpt hSy
    simp [witnessDecoded] at hSy
  · intro rid r callerTid hSy
    simp [witnessDecoded] at hSy
  · intro notifId hSy
    simp [witnessDecoded] at hSy
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecoded] at hSy
  · intro rid r callerTid hSy hTgt hR hCaller
    simp [witnessDecoded] at hSy

/-- The checked-tier pack is inhabited too: the base witness plus the
declassifying signal's confinement, vacuous at a `.send`-shaped decode. -/
theorem checkedSyscallDispatchQuiescence_inhabited :
    checkedSyscallDispatchQuiescence witnessDecoded witnessTid witnessGate
      witnessCap witnessSt3 :=
  ⟨syscallDispatchQuiescence_inhabited, by
    intro notifId hSy
    simp [witnessDecoded] at hSy⟩

-- ============================================================================
-- §7b  Per-arm exercise of the indexed pack fields (PR #886 review)
-- ============================================================================

/-! The base witness above inhabits both packs, but its `.send`-shaped decode
and `.replyCap`-shaped capability discharge every *indexed* field vacuously --
an unsatisfiable arm obligation would not have failed it.  The instances below
re-inhabit the packs once per indexed field with that field's premises firing,
so the family as a whole exercises every obligation the packs carry rather
than only the state-shaped ones.

Coverage, and the one boundary:

* `…_inhabited_signal` -- `signalNoBoundTarget` computes
  `boundDeliveryTarget? = none` on a present object;
* `…_inhabited_bind` / `…_inhabited_unbind` / `…_inhabited_suspend` -- the
  capability pack's arm-guarded fields under their own arms (PR #886
  review: the guards keep unrelated payloads from activating them):
  `boundThreadNotDonationOwner` read off the stored binding,
  `unbindBoundThreadPassive` firing its shape premises against the present
  object holding a TCB where a SchedContext is demanded, and
  `targetThreadQuiescent` proven of the *present* witness thread;
* `…_inhabited_retype` -- `retypeDetached` proven of the decoded target, and
  `boundThreadNotDonationOwner` firing through the bind decoder's read of
  the same registers;
* `…_inhabited_send` / `…_inhabited_receive` / `…_inhabited_call` -- each
  stage transition *evaluated* on the witness state (the refusal path), so
  the `objects.invExt` conclusions are discharged by computation; the
  receive resolver computes `.ok none`, and the call rendezvous field fires
  on the computed absent-endpoint lookup;
* `…_inhabited_mint` -- the mint decoder computes and its badge's validity
  is proven of the decoded value;
* `…_inhabited_reply` -- the `.reply` decode, the reply-capability target
  and the object lookup all fire against a stored reply (`witnessSt4`, the
  retype lever's fourth application).  **The lever boundary**: the
  remaining `caller = some _` premise cannot fire, because
  `retypeReplacementFresh` fixes a fresh reply's caller to `none` and only
  the call rendezvous creates a caller-carrying reply.  That interior --
  and `replyRecvStage`'s resolver premise, which needs a CSpace-resolved
  reply capability the same rendezvous supplies -- is the registered
  residual (WS-DT, `docs/WORKSTREAM_HISTORY.md`);
* `checked…_inhabited_declassifySignal` -- the checked tier's confinement
  computed on a present object, as the signal arm's is. -/

/-- A `.notificationSignal` decode: no registers, so every register-reading
decoder refuses and only the signal confinement fires. -/
private def witnessDecodedSignal : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := default,
    syscallId := .notificationSignal }

private def witnessGateSignal : SyscallGate :=
  { callerId := witnessTid, cspaceRoot := SeLe4n.ObjId.ofNat 0,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0,
    requiredRight := syscallRequiredRight .notificationSignal }

/-- An object capability naming the witness thread's own slot: present in the
store, so the object-target fields are exercised against a real object rather
than by absent-lookup vacuity. -/
private def witnessCapTcbObject : Capability :=
  { target := .object witnessTid.toObjId, rights := default }

private theorem witnessSt3_getNotification_tcbSlot :
    witnessSt3.getNotification? witnessTid.toObjId = none := by
  unfold SystemState.getNotification?
  rw [witnessSt3_lookup]
  simp [show (witnessScId.toObjId == witnessTid.toObjId) = false from by decide]

/-- The witness thread's IPC fields are quiescent -- proven of the *present*
thread, every field read off the stored TCB. -/
private theorem witnessThreadQuiescent :
    threadIpcFieldsQuiescent witnessSt3 witnessTid := by
  constructor
  all_goals intro tcb hLk
  all_goals rw [witnessSt3_getTcb] at hLk
  all_goals cases hLk
  all_goals simp [witnessTcbBound, witnessTcbFresh]

/-- The capability-only pack against the signal decode and the TCB-object
capability: the register decoders refuse (no registers), the SchedContext
target holds a TCB (a real shape contradiction, not an absent lookup), and
the thread-quiescence field is discharged by `witnessThreadQuiescent`. -/
private theorem witnessCapOnlySignal :
    capabilityDispatchQuiescence witnessDecodedSignal witnessCapTcbObject
      witnessSt3 := by
  refine ⟨witnessCapOnly.bindingBidirectional, witnessCapOnly.queuedThreadsIdle,
    ?_, ?_, ?_, ?_⟩
  · intro args _ hDec
    simp only [decodeLifecycleRetypeArgs, witnessDecodedSignal, requireMsgReg,
      bind, Except.bind] at hDec
    cases hDec
  · intro args _ hDec
    simp only [decodeSchedContextBindArgs, witnessDecodedSignal, requireMsgReg,
      bind, Except.bind] at hDec
    cases hDec
  · intro scObj _ hTgt vScId hVal scX t tcbX hScLk
    injection hTgt with hObj
    subst hObj
    simp only [validateObjIdArg, SeLe4n.ObjId.toValid?] at hVal
    rw [dif_neg (by decide)] at hVal
    cases hVal
    rw [show (SchedContextId.ofObjId witnessTid.toObjId).toObjId
        = witnessTid.toObjId from rfl, witnessSt3_lookup] at hScLk
    simp [show (witnessScId.toObjId == witnessTid.toObjId) = false from by decide]
      at hScLk
  · intro objId _ hTgt vtid hVal
    injection hTgt with hObj
    subst hObj
    simp only [validateThreadIdArg, SeLe4n.ThreadId.toValid?] at hVal
    rw [dif_neg (by decide)] at hVal
    cases hVal
    exact witnessThreadQuiescent

/-- **The signal arm's confinement is exercised**: the decode is
`.notificationSignal`, the target premise fires, and
`boundDeliveryTarget? = none` is computed on the present (non-notification)
object rather than assumed. -/
theorem syscallDispatchQuiescence_inhabited_signal :
    syscallDispatchQuiescence witnessDecodedSignal witnessTid witnessGateSignal
      witnessCapTcbObject witnessSt3 := by
  refine ⟨witnessReachable3, witnessCapOnlySignal,
    ⟨witnessTcbBound, witnessSt3_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp [witnessDecodedSignal] at hSy
  · intro epId hSy
    simp [witnessDecodedSignal] at hSy
  · intro epId hSy
    simp [witnessDecodedSignal] at hSy
  · intro epId hSy
    simp [witnessDecodedSignal] at hSy
  · intro epId replyIdOpt hSy
    simp [witnessDecodedSignal] at hSy
  · intro rid r callerTid hSy
    simp [witnessDecodedSignal] at hSy
  · intro notifId hSy hTgt
    injection hTgt with hObj
    subst hObj
    unfold boundDeliveryTarget?
    rw [witnessSt3_getNotification_tcbSlot]
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecodedSignal] at hSy
  · intro rid r callerTid hSy hTgt hR hCaller
    simp [witnessDecodedSignal] at hSy

/-- A `.lifecycleRetype` decode whose registers decode: target `⟨9⟩`
(referenced by nothing), type tag 5 (`.untyped`), size 0.  The bind decoder
reads the same register file, so `boundThreadNotDonationOwner` fires through
it in the same instance. -/
private def witnessDecodedRetype : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := default,
    syscallId := .lifecycleRetype, msgRegs := #[⟨9⟩, ⟨5⟩, ⟨0⟩] }

private def witnessGateRetype : SyscallGate :=
  { callerId := witnessTid, cspaceRoot := SeLe4n.ObjId.ofNat 0,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0,
    requiredRight := syscallRequiredRight .lifecycleRetype }

/-- Every stored TCB is the witness thread's: the store's one TCB slot,
characterised for the detachedness fields that quantify over the store. -/
private theorem witnessSt3_tcb_lookup (oid : SeLe4n.ObjId) (t : TCB)
    (hLk : witnessSt3.objects[oid]? = some (.tcb t)) :
    oid = witnessTid.toObjId ∧ t = witnessTcbBound := by
  rw [witnessSt3_lookup] at hLk
  split at hLk
  · cases hLk
  · split at hLk
    · next hKey => cases hLk; exact ⟨(eq_of_beq hKey).symm, rfl⟩
    · cases hLk

private theorem witnessSt3_no_endpoint (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hLk : witnessSt3.objects[oid]? = some (.endpoint ep)) : False := by
  rw [witnessSt3_lookup] at hLk
  split at hLk
  · simp at hLk
  · split at hLk
    · simp at hLk
    · cases hLk

private theorem witnessSt3_no_notification (oid : SeLe4n.ObjId) (n : Notification)
    (hLk : witnessSt3.objects[oid]? = some (.notification n)) : False := by
  rw [witnessSt3_lookup] at hLk
  split at hLk
  · simp at hLk
  · split at hLk
    · simp at hLk
    · cases hLk

private theorem witnessSt3_lookup_none (oid : SeLe4n.ObjId)
    (hSc : (witnessScId.toObjId == oid) = false)
    (hTid : (witnessTid.toObjId == oid) = false) :
    witnessSt3.objects[oid]? = none := by
  rw [witnessSt3_lookup]
  simp [hSc, hTid]

/-- Nothing in the witness state references an empty slot: detachedness of
any target outside the two stored ids, proven once and instantiated per
consumer.  The target-lookup fields discharge on the empty slot; the
store-quantified fields read the one stored TCB's quiescent shape through
`witnessSt3_tcb_lookup`. -/
private theorem witnessSt3_detached_of (target : SeLe4n.ObjId)
    (hSc : (witnessScId.toObjId == target) = false)
    (hTid : (witnessTid.toObjId == target) = false) :
    retypeTargetDetached witnessSt3 target := by
  have hTargetEmpty := witnessSt3_lookup_none target hSc hTid
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sc; rw [hTargetEmpty]; simp
  · intro t hLk; rw [hTargetEmpty] at hLk; cases hLk
  · intro t hLk; rw [hTargetEmpty] at hLk; cases hLk
  · intro t hLk; rw [hTargetEmpty] at hLk; cases hLk
  · intro t hLk; rw [hTargetEmpty] at hLk; cases hLk
  · intro t hLk; rw [hTargetEmpty] at hLk; cases hLk
  · intro t hLk; rw [hTargetEmpty] at hLk; cases hLk
  · intro t hLk; rw [hTargetEmpty] at hLk; cases hLk
  · intro t hLk; rw [hTargetEmpty] at hLk; cases hLk
  · intro tid tcb hLk
    obtain ⟨-, rfl⟩ := witnessSt3_tcb_lookup _ _ hLk
    refine ⟨?_, ?_, ?_⟩ <;> simp [witnessTcbBound, witnessTcbFresh]
  · intro a tcbA b hLk hNext
    obtain ⟨-, rfl⟩ := witnessSt3_tcb_lookup _ _ hLk
    simp [witnessTcbBound, witnessTcbFresh] at hNext
  · intro b tcbB a hLk hPrev
    obtain ⟨-, rfl⟩ := witnessSt3_tcb_lookup _ _ hLk
    simp [witnessTcbBound, witnessTcbFresh] at hPrev
  · intro epId ep hd hLk
    exact absurd hLk (fun h => witnessSt3_no_endpoint _ _ h)
  · intro epId ep tl hLk
    exact absurd hLk (fun h => witnessSt3_no_endpoint _ _ h)
  · intro tid tcb hLk
    obtain ⟨-, rfl⟩ := witnessSt3_tcb_lookup _ _ hLk
    simp [witnessTcbBound, witnessTcbFresh]
  · intro tid tcb rid hLk hReply
    obtain ⟨-, rfl⟩ := witnessSt3_tcb_lookup _ _ hLk
    simp [witnessTcbBound, witnessTcbFresh] at hReply
  · intro tid tcb rid hLk hStash
    obtain ⟨-, rfl⟩ := witnessSt3_tcb_lookup _ _ hLk
    simp [witnessTcbBound, witnessTcbFresh] at hStash

/-- The capability-only pack against the retype decode: `retypeDetached` is
proven of the decoded target rather than discharged by a failing decoder,
and the bind-decoder field fires (same registers) with its donation
conclusion read off the stored binding. -/
private theorem witnessCapOnlyRetype :
    capabilityDispatchQuiescence witnessDecodedRetype witnessCap witnessSt3 := by
  refine ⟨witnessCapOnly.bindingBidirectional, witnessCapOnly.queuedThreadsIdle,
    ?_, ?_, ?_, ?_⟩
  · intro args _ hDec
    simp only [decodeLifecycleRetypeArgs, witnessDecodedRetype, requireMsgReg,
      bind, Except.bind, pure, Except.pure, KernelObjectType.ofNat?] at hDec
    cases hDec
    exact witnessSt3_detached_of _ (by decide) (by decide)
  · intro args _ hDec vThreadId hVal s sTcb sc0 hLk
    rw [witnessSt3_lookup] at hLk
    split at hLk
    · cases hLk
    · split at hLk
      · cases hLk
        simp [witnessTcbBound, witnessTcbFresh]
      · cases hLk
  · intro scObj _ hTgt
    simp [witnessCap] at hTgt
  · intro objId _ hTgt
    simp [witnessCap] at hTgt

/-- **The retype detachment is exercised**: the registers decode, the target
is named, and detachedness is proven of the witness state -- with the bind
decoder's donation field firing through the same register file. -/
theorem syscallDispatchQuiescence_inhabited_retype :
    syscallDispatchQuiescence witnessDecodedRetype witnessTid witnessGateRetype
      witnessCap witnessSt3 := by
  refine ⟨witnessReachable3, witnessCapOnlyRetype,
    ⟨witnessTcbBound, witnessSt3_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp [witnessDecodedRetype] at hSy
  · intro epId hSy
    simp [witnessDecodedRetype] at hSy
  · intro epId hSy
    simp [witnessDecodedRetype] at hSy
  · intro epId hSy
    simp [witnessDecodedRetype] at hSy
  · intro epId replyIdOpt hSy
    simp [witnessDecodedRetype] at hSy
  · intro rid r callerTid hSy
    simp [witnessDecodedRetype] at hSy
  · intro notifId hSy
    simp [witnessDecodedRetype] at hSy
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecodedRetype] at hSy
  · intro rid r callerTid hSy hTgt hR hCaller
    simp [witnessDecodedRetype] at hSy

/-- An object capability naming slot `⟨7⟩` -- no endpoint lives there, so the
stage transitions evaluate down their refusal paths and their `invExt`
conclusions are discharged by computation on the witness state. -/
private def witnessCapEndpoint : Capability :=
  { target := .object (SeLe4n.ObjId.ofNat 7), rights := default }

private theorem witnessSt3_lookup_seven :
    witnessSt3.objects[(SeLe4n.ObjId.ofNat 7 : SeLe4n.ObjId)]? = none := by
  rw [witnessSt3_lookup]
  simp [show (witnessScId.toObjId == SeLe4n.ObjId.ofNat 7) = false from by decide,
    show (witnessTid.toObjId == SeLe4n.ObjId.ofNat 7) = false from by decide]

private theorem witnessSt3_getTcb_seven :
    witnessSt3.getTcb?
      (SeLe4n.ThreadId.ofNat (SeLe4n.ObjId.ofNat 7).toNat) = none := by
  unfold SystemState.getTcb?
  rw [show (SeLe4n.ThreadId.ofNat
      (SeLe4n.ObjId.ofNat 7).toNat).toObjId = SeLe4n.ObjId.ofNat 7 from rfl,
    witnessSt3_lookup_seven]

/-- The capability-only pack against any register-free decode and the absent
endpoint capability: the decoders refuse on the empty register file, and the
object-target fields discharge on the empty slot. -/
private theorem witnessCapOnlyEndpointOf (decoded : SyscallDecodeResult)
    (hRegs : decoded.msgRegs = #[]) :
    capabilityDispatchQuiescence decoded witnessCapEndpoint witnessSt3 := by
  refine ⟨witnessCapOnly.bindingBidirectional, witnessCapOnly.queuedThreadsIdle,
    ?_, ?_, ?_, ?_⟩
  · intro args _ hDec
    simp only [decodeLifecycleRetypeArgs, hRegs, requireMsgReg, bind,
      Except.bind] at hDec
    cases hDec
  · intro args _ hDec
    simp only [decodeSchedContextBindArgs, hRegs, requireMsgReg, bind,
      Except.bind] at hDec
    cases hDec
  · intro scObj _ hTgt vScId hVal scX t tcbX hScLk
    injection hTgt with hObj
    subst hObj
    simp only [validateObjIdArg, SeLe4n.ObjId.toValid?] at hVal
    rw [dif_neg (by decide)] at hVal
    cases hVal
    rw [show (SchedContextId.ofObjId (SeLe4n.ObjId.ofNat 7)).toObjId
        = SeLe4n.ObjId.ofNat 7 from rfl, witnessSt3_lookup_seven] at hScLk
    cases hScLk
  · intro objId _ hTgt vtid hVal
    injection hTgt with hObj
    subst hObj
    simp only [validateThreadIdArg, SeLe4n.ThreadId.toValid?] at hVal
    rw [dif_neg (by decide)] at hVal
    cases hVal
    constructor
    all_goals intro tcb hLk
    all_goals rw [witnessSt3_getTcb_seven] at hLk
    all_goals cases hLk

/-- **The send stage is exercised**: the `.send` decode and the object target
both fire, and the staged transition's `invExt` conclusion is discharged by
evaluating the transition on the witness state -- the refusal path returns
the state whose invariant is already proven. -/
theorem syscallDispatchQuiescence_inhabited_send :
    syscallDispatchQuiescence witnessDecoded witnessTid witnessGate
      witnessCapEndpoint witnessSt3 := by
  refine ⟨witnessReachable3, witnessCapOnlyEndpointOf witnessDecoded rfl,
    ⟨witnessTcbBound, witnessSt3_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp [witnessDecoded] at hSy
  · intro epId hSy hTgt
    injection hTgt with hObj
    subst hObj
    intro st1 res hStep
    obtain rfl : st1 = _ := (congrArg Prod.fst hStep).symm
    exact witnessObjInv3
  · intro epId hSy
    simp [witnessDecoded] at hSy
  · intro epId hSy
    simp [witnessDecoded] at hSy
  · intro epId replyIdOpt hSy
    simp [witnessDecoded] at hSy
  · intro rid r callerTid hSy
    simp [witnessDecoded] at hSy
  · intro notifId hSy
    simp [witnessDecoded] at hSy
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecoded] at hSy
  · intro rid r callerTid hSy hTgt hR hCaller
    simp [witnessDecoded] at hSy

/-- A `.receive` decode with an explicit zero-length message info: the reply
resolver's length gate reduces syntactically, so the premise fires with
`replyIdOpt = none`. -/
private def witnessDecodedRecv : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0,
    msgInfo := { length := 0, extraCaps := 0, label := 0 },
    syscallId := .receive }

private def witnessGateRecv : SyscallGate :=
  { callerId := witnessTid, cspaceRoot := SeLe4n.ObjId.ofNat 0,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0,
    requiredRight := syscallRequiredRight .receive }

/-- **The receive stage is exercised**: the resolver computes `.ok none`, the
delivered-caps conjunct reads the stored TCB (no pending message), and the
transition's `invExt` conclusion is discharged by evaluation on the witness
state. -/
theorem syscallDispatchQuiescence_inhabited_receive :
    syscallDispatchQuiescence witnessDecodedRecv witnessTid witnessGateRecv
      witnessCapEndpoint witnessSt3 := by
  refine ⟨witnessReachable3, witnessCapOnlyEndpointOf witnessDecodedRecv rfl,
    ⟨witnessTcbBound, witnessSt3_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp [witnessDecodedRecv] at hSy
  · intro epId hSy
    simp [witnessDecodedRecv] at hSy
  · intro epId hSy
    simp [witnessDecodedRecv] at hSy
  · intro epId hSy
    simp [witnessDecodedRecv] at hSy
  · intro epId replyIdOpt hSy hTgt hRes
    injection hTgt with hObj
    subst hObj
    simp only [resolveRecvReplyId, witnessDecodedRecv] at hRes
    injection hRes with hOpt
    subst hOpt
    refine ⟨?_, ?_, ?_⟩
    · intro rid h; cases h
    · intro tcb hTcb m hMsg
      cases Option.some.inj (witnessSt3_getTcb.symm.trans hTcb)
      simp [witnessTcbBound, witnessTcbFresh] at hMsg
    · intro st1 res hStep
      obtain rfl : st1 = _ := (congrArg Prod.fst hStep).symm
      exact witnessObjInv3
  · intro rid r callerTid hSy
    simp [witnessDecodedRecv] at hSy
  · intro notifId hSy
    simp [witnessDecodedRecv] at hSy
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecodedRecv] at hSy
  · intro rid r callerTid hSy hTgt hR hCaller
    simp [witnessDecodedRecv] at hSy

/-- A `.call` decode: no registers, absent endpoint target. -/
private def witnessDecodedCall : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := default, syscallId := .call }

private def witnessGateCall : SyscallGate :=
  { callerId := witnessTid, cspaceRoot := SeLe4n.ObjId.ofNat 0,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0,
    requiredRight := syscallRequiredRight .call }

private theorem witnessSt3_getEndpoint_seven :
    witnessSt3.getEndpoint? (SeLe4n.ObjId.ofNat 7) = none := by
  unfold SystemState.getEndpoint?
  rw [witnessSt3_lookup_seven]

/-- **The call stage is exercised**: both call fields fire on the endpoint
target -- the cross-core dispatch's `invExt` conclusion by evaluation, and
the rendezvous field on the computed absent-endpoint lookup. -/
theorem syscallDispatchQuiescence_inhabited_call :
    syscallDispatchQuiescence witnessDecodedCall witnessTid witnessGateCall
      witnessCapEndpoint witnessSt3 := by
  refine ⟨witnessReachable3, witnessCapOnlyEndpointOf witnessDecodedCall rfl,
    ⟨witnessTcbBound, witnessSt3_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp [witnessDecodedCall] at hSy
  · intro epId hSy
    simp [witnessDecodedCall] at hSy
  · intro epId hSy hTgt
    injection hTgt with hObj
    subst hObj
    intro st1 res hStep
    obtain rfl : st1 = _ := (congrArg Prod.fst hStep).symm
    exact witnessObjInv3
  · intro epId hSy hTgt
    injection hTgt with hObj
    subst hObj
    intro ep receiverTid hEp
    rw [witnessSt3_getEndpoint_seven] at hEp
    cases hEp
  · intro epId replyIdOpt hSy
    simp [witnessDecodedCall] at hSy
  · intro rid r callerTid hSy
    simp [witnessDecodedCall] at hSy
  · intro notifId hSy
    simp [witnessDecodedCall] at hSy
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecodedCall] at hSy
  · intro rid r callerTid hSy hTgt hR hCaller
    simp [witnessDecodedCall] at hSy

/-- A `.cspaceMint` decode whose registers decode: srcSlot 0 (also the bind
decoder's thread id -- the sentinel, so that field refuses at validation),
dstSlot 999 (also the retype decoder's type tag -- invalid, so that decoder
refuses), rights word 3, badge word 5. -/
private def witnessDecodedMint : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := default,
    syscallId := .cspaceMint, msgRegs := #[⟨0⟩, ⟨999⟩, ⟨3⟩, ⟨5⟩] }

private def witnessGateMint : SyscallGate :=
  { callerId := witnessTid, cspaceRoot := SeLe4n.ObjId.ofNat 0,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0,
    requiredRight := syscallRequiredRight .cspaceMint }

private theorem witnessCapOnlyMint :
    capabilityDispatchQuiescence witnessDecodedMint witnessCap witnessSt3 := by
  refine ⟨witnessCapOnly.bindingBidirectional, witnessCapOnly.queuedThreadsIdle,
    ?_, ?_, ?_, ?_⟩
  · intro args _ hDec
    simp only [decodeLifecycleRetypeArgs, witnessDecodedMint, requireMsgReg,
      bind, Except.bind, pure, Except.pure, KernelObjectType.ofNat?] at hDec
    cases hDec
  · intro args _ hDec vThreadId hVal
    simp only [decodeSchedContextBindArgs, witnessDecodedMint, requireMsgReg,
      bind, Except.bind, pure, Except.pure] at hDec
    cases hDec
    simp only [validateThreadIdArg, SeLe4n.ThreadId.toValid?] at hVal
    rw [dif_pos (by decide)] at hVal
    cases hVal
  · intro scObj _ hTgt
    simp [witnessCap] at hTgt
  · intro objId _ hTgt
    simp [witnessCap] at hTgt

/-- **The mint badge validity is exercised**: the registers decode and the
decoded badge's validity is computed. -/
theorem syscallDispatchQuiescence_inhabited_mint :
    syscallDispatchQuiescence witnessDecodedMint witnessTid witnessGateMint
      witnessCap witnessSt3 := by
  refine ⟨witnessReachable3, witnessCapOnlyMint,
    ⟨witnessTcbBound, witnessSt3_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp only [Architecture.SyscallArgDecode.decodeCSpaceMintArgs,
      witnessDecodedMint, requireMsgReg, bind, Except.bind, pure,
      Except.pure] at hDec
    split at hDec
    · cases hDec
    · injection hDec with hArgs
      subst hArgs
      exact SeLe4n.Badge.ofNatMasked_valid _
  · intro epId hSy
    simp [witnessDecodedMint] at hSy
  · intro epId hSy
    simp [witnessDecodedMint] at hSy
  · intro epId hSy
    simp [witnessDecodedMint] at hSy
  · intro epId replyIdOpt hSy
    simp [witnessDecodedMint] at hSy
  · intro rid r callerTid hSy
    simp [witnessDecodedMint] at hSy
  · intro notifId hSy
    simp [witnessDecodedMint] at hSy
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecodedMint] at hSy
  · intro rid r callerTid hSy hTgt hR hCaller
    simp [witnessDecodedMint] at hSy

/-- A `.declassifySignal` decode: the checked tier's confinement fires. -/
private def witnessDecodedDeclassifySignal : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := default,
    syscallId := .declassifySignal }

private def witnessGateDeclassifySignal : SyscallGate :=
  { callerId := witnessTid, cspaceRoot := SeLe4n.ObjId.ofNat 0,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0,
    requiredRight := syscallRequiredRight .declassifySignal }

private theorem witnessCapOnlyDeclassifySignal :
    capabilityDispatchQuiescence witnessDecodedDeclassifySignal
      witnessCapTcbObject witnessSt3 := by
  refine ⟨witnessCapOnly.bindingBidirectional, witnessCapOnly.queuedThreadsIdle,
    ?_, ?_, ?_, ?_⟩
  · intro args _ hDec
    simp only [decodeLifecycleRetypeArgs, witnessDecodedDeclassifySignal,
      requireMsgReg, bind, Except.bind] at hDec
    cases hDec
  · intro args _ hDec
    simp only [decodeSchedContextBindArgs, witnessDecodedDeclassifySignal,
      requireMsgReg, bind, Except.bind] at hDec
    cases hDec
  · intro scObj _ hTgt vScId hVal scX t tcbX hScLk
    injection hTgt with hObj
    subst hObj
    simp only [validateObjIdArg, SeLe4n.ObjId.toValid?] at hVal
    rw [dif_neg (by decide)] at hVal
    cases hVal
    rw [show (SchedContextId.ofObjId witnessTid.toObjId).toObjId
        = witnessTid.toObjId from rfl, witnessSt3_lookup] at hScLk
    simp [show (witnessScId.toObjId == witnessTid.toObjId) = false from by decide]
      at hScLk
  · intro objId _ hTgt vtid hVal
    injection hTgt with hObj
    subst hObj
    simp only [validateThreadIdArg, SeLe4n.ThreadId.toValid?] at hVal
    rw [dif_neg (by decide)] at hVal
    cases hVal
    exact witnessThreadQuiescent

private theorem syscallDispatchQuiescence_inhabited_declassifySignal :
    syscallDispatchQuiescence witnessDecodedDeclassifySignal witnessTid
      witnessGateDeclassifySignal witnessCapTcbObject witnessSt3 := by
  refine ⟨witnessReachable3, witnessCapOnlyDeclassifySignal,
    ⟨witnessTcbBound, witnessSt3_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp [witnessDecodedDeclassifySignal] at hSy
  · intro epId hSy
    simp [witnessDecodedDeclassifySignal] at hSy
  · intro epId hSy
    simp [witnessDecodedDeclassifySignal] at hSy
  · intro epId hSy
    simp [witnessDecodedDeclassifySignal] at hSy
  · intro epId replyIdOpt hSy
    simp [witnessDecodedDeclassifySignal] at hSy
  · intro rid r callerTid hSy
    simp [witnessDecodedDeclassifySignal] at hSy
  · intro notifId hSy
    simp [witnessDecodedDeclassifySignal] at hSy
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecodedDeclassifySignal] at hSy
  · intro rid r callerTid hSy hTgt hR hCaller
    simp [witnessDecodedDeclassifySignal] at hSy

/-- **The checked confinement is exercised**: the `.declassifySignal` decode
and the object target both fire, and `boundDeliveryTarget? = none` is
computed on the present object. -/
theorem checkedSyscallDispatchQuiescence_inhabited_declassifySignal :
    checkedSyscallDispatchQuiescence witnessDecodedDeclassifySignal witnessTid
      witnessGateDeclassifySignal witnessCapTcbObject witnessSt3 :=
  ⟨syscallDispatchQuiescence_inhabited_declassifySignal, by
    intro notifId hSy hTgt
    injection hTgt with hObj
    subst hObj
    unfold boundDeliveryTarget?
    rw [witnessSt3_getNotification_tcbSlot]⟩

/-- A fresh reply object at slot `⟨3⟩`: the reply arm's object-lookup premise
fires against a real stored reply.  Its `caller` is `none` -- the retype
lever's freshness constraint (`retypeReplacementFresh`) forbids minting a
caller-carrying reply, because in the live kernel only the call rendezvous
creates one; the reply field is therefore exercised exactly to the lever
boundary, and the caller-carrying interior is registered debt (see the
section docstring). -/
private def witnessReplyId : SeLe4n.ReplyId :=
  SeLe4n.ReplyId.ofObjId (SeLe4n.ObjId.ofNat 3)

private def witnessReplyFresh : Reply := { replyId := witnessReplyId }

private def witnessSt4 : SystemState :=
  { witnessSt3 with
    objects := witnessSt3.objects.insert (SeLe4n.ObjId.ofNat 3)
      (.reply witnessReplyFresh) }

private theorem witnessObjInv4 : witnessSt4.objects.invExt :=
  RHTable_insert_preserves_invExt _ _ _ witnessObjInv3

private theorem witnessSt4_lookup (oid : SeLe4n.ObjId) :
    witnessSt4.objects[oid]?
      = if (SeLe4n.ObjId.ofNat 3 : SeLe4n.ObjId) == oid
        then some (.reply witnessReplyFresh)
        else witnessSt3.objects[oid]? := by
  show (witnessSt3.objects.insert (SeLe4n.ObjId.ofNat 3)
      (.reply witnessReplyFresh))[oid]? = _
  rw [RHTable_getElem?_eq_get?,
    RHTable_getElem?_insert _ _ _ witnessObjInv3]
  split
  · rfl
  · rw [← RHTable_getElem?_eq_get?]

private theorem witnessInv4 : ipcInvariantFull witnessSt4 := by
  refine retypeWrite_preserves_ipcInvariantFull (st := witnessSt3)
    (target := SeLe4n.ObjId.ofNat 3) (newObj := .reply witnessReplyFresh)
    ?_ ?_ rfl rfl (witnessSt3_detached_of _ (by decide) (by decide)) witnessInv3
  · rw [witnessSt4_lookup]; simp
  · intro oid hne
    rw [witnessSt4_lookup]
    simp [Ne.symm hne]

set_option maxHeartbeats 1000000 in
private theorem witnessReachable4 : ipcReachable witnessSt4 := by
  refine ⟨witnessInv4, witnessObjInv4, ?_, ?_, ?_⟩
  · intro tid tcb hLk
    rw [witnessSt4_lookup] at hLk
    split at hLk
    · cases hLk
    · exact witnessReachable3.allTimeoutBudgetsNone _ _ hLk
  · intro tid tcb msg hLk hMsg
    rw [witnessSt4_lookup] at hLk
    split at hLk
    · cases hLk
    · exact witnessReachable3.pendingMessageCapBadgesWellFormed _ _ _ hLk hMsg
  · intro oid ntfn tid hLk hMem
    rw [witnessSt4_lookup] at hLk
    split at hLk
    · cases hLk
    · exact absurd hLk (fun h => witnessSt3_no_notification _ _ h)

private theorem witnessSt4_getTcb :
    witnessSt4.getTcb? witnessTid = some witnessTcbBound := by
  unfold SystemState.getTcb?
  rw [witnessSt4_lookup, witnessSt3_lookup]
  simp [show ((SeLe4n.ObjId.ofNat 3 : SeLe4n.ObjId) == witnessTid.toObjId)
      = false from by decide,
    show (witnessScId.toObjId == witnessTid.toObjId) = false from by decide]

private theorem witnessSt4_getReply :
    witnessSt4.getReply? witnessReplyId = some witnessReplyFresh := by
  unfold SystemState.getReply?
  rw [show witnessReplyId.toObjId = SeLe4n.ObjId.ofNat 3 from rfl,
    witnessSt4_lookup]
  simp

/-- WS-RR RR4.14: no thread in the reply witness carries a pending fault — the
witness TCBs are built from `witnessTcbFresh`, whose `pendingFault` is the field
default `none`.  This is what discharges the pack's `replyNoPendingFault`
confinement at the `.reply` instance, so the field is inhabited rather than
vacuously satisfiable. -/
private theorem witnessSt4_no_pendingFault (tid : SeLe4n.ThreadId) :
    threadHasPendingFault witnessSt4 tid = false := by
  rw [threadHasPendingFault_eq_false_iff]
  intro tcb hTcb
  rw [SystemState.getTcb?_eq_some_iff, witnessSt4_lookup] at hTcb
  split at hTcb
  · simp at hTcb
  · rw [witnessSt3_lookup] at hTcb
    split at hTcb
    · simp at hTcb
    · split at hTcb
      · have hEq : tcb = witnessTcbBound := by simpa using hTcb.symm
        subst hEq; rfl
      · simp at hTcb

/-- A `.reply` decode and the reply capability naming the stored object. -/
private def witnessDecodedReply : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := default, syscallId := .reply }

private def witnessGateReply : SyscallGate :=
  { callerId := witnessTid, cspaceRoot := SeLe4n.ObjId.ofNat 0,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0,
    requiredRight := syscallRequiredRight .reply }

private def witnessCapReply : Capability :=
  { target := .replyCap witnessReplyId, rights := default }

private theorem witnessCapOnlyReply :
    capabilityDispatchQuiescence witnessDecodedReply witnessCapReply
      witnessSt4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t tcb scId hLk hScId
    rw [witnessSt4_lookup] at hLk
    split at hLk
    · cases hLk
    · have := witnessCapOnly.bindingBidirectional t tcb scId hLk hScId
      obtain ⟨scObj, hScLk, hBack⟩ := this
      refine ⟨scObj, ?_, hBack⟩
      rw [witnessSt4_lookup, if_neg ?_]
      · exact hScLk
      · intro hEq
        rw [witnessSt3_lookup] at hScLk
        rw [show scId.toObjId = SeLe4n.ObjId.ofNat 3 from (eq_of_beq hEq).symm]
          at hScLk
        simp [show (witnessScId.toObjId == SeLe4n.ObjId.ofNat 3) = false from
          by decide,
          show (witnessTid.toObjId == SeLe4n.ObjId.ofNat 3) = false from
          by decide] at hScLk
  · intro c t tcb hLk hUnbound hCur
    rw [witnessSt4_lookup] at hLk
    split at hLk
    · cases hLk
    · exact witnessCapOnly.queuedThreadsIdle c t tcb hLk hUnbound hCur
  · intro args _ hDec
    simp only [decodeLifecycleRetypeArgs, witnessDecodedReply, requireMsgReg,
      bind, Except.bind] at hDec
    cases hDec
  · intro args _ hDec
    simp only [decodeSchedContextBindArgs, witnessDecodedReply, requireMsgReg,
      bind, Except.bind] at hDec
    cases hDec
  · intro scObj _ hTgt
    simp [witnessCapReply] at hTgt
  · intro objId _ hTgt
    simp [witnessCapReply] at hTgt

/-- **The reply arm is exercised to the lever boundary**: the `.reply`
decode, the reply-capability target and the object lookup all fire against
the stored reply; the remaining `caller = some _` premise is where the
retype lever's freshness constraint stops (only the call rendezvous creates
a caller-carrying reply). -/
theorem syscallDispatchQuiescence_inhabited_reply :
    syscallDispatchQuiescence witnessDecodedReply witnessTid witnessGateReply
      witnessCapReply witnessSt4 := by
  refine ⟨witnessReachable4, witnessCapOnlyReply,
    ⟨witnessTcbBound, witnessSt4_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp [witnessDecodedReply] at hSy
  · intro epId hSy
    simp [witnessDecodedReply] at hSy
  · intro epId hSy
    simp [witnessDecodedReply] at hSy
  · intro epId hSy
    simp [witnessDecodedReply] at hSy
  · intro epId replyIdOpt hSy
    simp [witnessDecodedReply] at hSy
  · intro rid r callerTid hSy hTgt hReply hCaller
    injection hTgt with hRid
    subst hRid
    cases Option.some.inj (witnessSt4_getReply.symm.trans hReply)
    simp [witnessReplyFresh] at hCaller
  · intro notifId hSy
    simp [witnessDecodedReply] at hSy
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecodedReply] at hSy
  · intro rid r callerTid _hSy _hTgt hR hCaller
    -- WS-RR RR4.14: the witness state carries no faulted thread at all,
    -- so the confinement holds for whatever caller the reply resolves to.
    exact witnessSt4_no_pendingFault callerTid

/-- A `.schedContextBind` decode whose one register decodes (thread id 5,
valid): the bind field's donation conclusion is read off the stored binding
under its own arm. -/
private def witnessDecodedBind : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := default,
    syscallId := .schedContextBind, msgRegs := #[⟨5⟩] }

private def witnessGateBind : SyscallGate :=
  { callerId := witnessTid, cspaceRoot := SeLe4n.ObjId.ofNat 0,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0,
    requiredRight := syscallRequiredRight .schedContextBind }

private theorem witnessCapOnlyBind :
    capabilityDispatchQuiescence witnessDecodedBind witnessCap witnessSt3 := by
  refine ⟨witnessCapOnly.bindingBidirectional, witnessCapOnly.queuedThreadsIdle,
    ?_, ?_, ?_, ?_⟩
  · intro args _ hDec
    simp only [decodeLifecycleRetypeArgs, witnessDecodedBind, requireMsgReg,
      bind, Except.bind] at hDec
    cases hDec
  · intro args _ hDec vThreadId hVal s sTcb sc0 hLk
    rw [witnessSt3_lookup] at hLk
    split at hLk
    · cases hLk
    · split at hLk
      · cases hLk
        simp [witnessTcbBound, witnessTcbFresh]
      · cases hLk
  · intro scObj _ hTgt
    simp [witnessCap] at hTgt
  · intro objId _ hTgt
    simp [witnessCap] at hTgt

/-- **The bind donation field is exercised under its own arm**: the
`.schedContextBind` decode fires, the register decodes, and the conclusion
is read off the stored binding. -/
theorem syscallDispatchQuiescence_inhabited_bind :
    syscallDispatchQuiescence witnessDecodedBind witnessTid witnessGateBind
      witnessCap witnessSt3 := by
  refine ⟨witnessReachable3, witnessCapOnlyBind,
    ⟨witnessTcbBound, witnessSt3_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp [witnessDecodedBind] at hSy
  · intro epId hSy
    simp [witnessDecodedBind] at hSy
  · intro epId hSy
    simp [witnessDecodedBind] at hSy
  · intro epId hSy
    simp [witnessDecodedBind] at hSy
  · intro epId replyIdOpt hSy
    simp [witnessDecodedBind] at hSy
  · intro rid r callerTid hSy
    simp [witnessDecodedBind] at hSy
  · intro notifId hSy
    simp [witnessDecodedBind] at hSy
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecodedBind] at hSy
  · intro rid r callerTid hSy hTgt hR hCaller
    simp [witnessDecodedBind] at hSy

/-- A `.schedContextUnbind` decode with the TCB-object capability: the unbind
field's shape premises fire against the present (non-SchedContext) object. -/
private def witnessDecodedUnbind : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := default,
    syscallId := .schedContextUnbind }

private def witnessGateUnbind : SyscallGate :=
  { callerId := witnessTid, cspaceRoot := SeLe4n.ObjId.ofNat 0,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0,
    requiredRight := syscallRequiredRight .schedContextUnbind }

private theorem witnessCapOnlyUnbind :
    capabilityDispatchQuiescence witnessDecodedUnbind witnessCapTcbObject
      witnessSt3 := by
  refine ⟨witnessCapOnly.bindingBidirectional, witnessCapOnly.queuedThreadsIdle,
    ?_, ?_, ?_, ?_⟩
  · intro args _ hDec
    simp only [decodeLifecycleRetypeArgs, witnessDecodedUnbind, requireMsgReg,
      bind, Except.bind] at hDec
    cases hDec
  · intro args _ hDec
    simp only [decodeSchedContextBindArgs, witnessDecodedUnbind, requireMsgReg,
      bind, Except.bind] at hDec
    cases hDec
  · intro scObj _ hTgt vScId hVal scX t tcbX hScLk
    injection hTgt with hObj
    subst hObj
    simp only [validateObjIdArg, SeLe4n.ObjId.toValid?] at hVal
    rw [dif_neg (by decide)] at hVal
    cases hVal
    rw [show (SchedContextId.ofObjId witnessTid.toObjId).toObjId
        = witnessTid.toObjId from rfl, witnessSt3_lookup] at hScLk
    simp [show (witnessScId.toObjId == witnessTid.toObjId) = false from by decide]
      at hScLk
  · intro objId hSy hTgt
    rcases hSy with hSy | hSy <;> simp [witnessDecodedUnbind] at hSy

/-- **The unbind passivity field is exercised under its own arm**: the shape
premises fire against the present object holding a TCB where a SchedContext
is demanded. -/
theorem syscallDispatchQuiescence_inhabited_unbind :
    syscallDispatchQuiescence witnessDecodedUnbind witnessTid witnessGateUnbind
      witnessCapTcbObject witnessSt3 := by
  refine ⟨witnessReachable3, witnessCapOnlyUnbind,
    ⟨witnessTcbBound, witnessSt3_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp [witnessDecodedUnbind] at hSy
  · intro epId hSy
    simp [witnessDecodedUnbind] at hSy
  · intro epId hSy
    simp [witnessDecodedUnbind] at hSy
  · intro epId hSy
    simp [witnessDecodedUnbind] at hSy
  · intro epId replyIdOpt hSy
    simp [witnessDecodedUnbind] at hSy
  · intro rid r callerTid hSy
    simp [witnessDecodedUnbind] at hSy
  · intro notifId hSy
    simp [witnessDecodedUnbind] at hSy
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecodedUnbind] at hSy
  · intro rid r callerTid hSy hTgt hR hCaller
    simp [witnessDecodedUnbind] at hSy

/-- A `.tcbSuspend` decode with the TCB-object capability: the
thread-quiescence field fires under its own arm and is proven of the
present witness thread. -/
private def witnessDecodedSuspend : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := default,
    syscallId := .tcbSuspend }

private def witnessGateSuspend : SyscallGate :=
  { callerId := witnessTid, cspaceRoot := SeLe4n.ObjId.ofNat 0,
    capAddr := SeLe4n.CPtr.ofNat 0, capDepth := 0,
    requiredRight := syscallRequiredRight .tcbSuspend }

private theorem witnessCapOnlySuspend :
    capabilityDispatchQuiescence witnessDecodedSuspend witnessCapTcbObject
      witnessSt3 := by
  refine ⟨witnessCapOnly.bindingBidirectional, witnessCapOnly.queuedThreadsIdle,
    ?_, ?_, ?_, ?_⟩
  · intro args _ hDec
    simp only [decodeLifecycleRetypeArgs, witnessDecodedSuspend, requireMsgReg,
      bind, Except.bind] at hDec
    cases hDec
  · intro args _ hDec
    simp only [decodeSchedContextBindArgs, witnessDecodedSuspend, requireMsgReg,
      bind, Except.bind] at hDec
    cases hDec
  · intro scObj hSy hTgt
    simp [witnessDecodedSuspend] at hSy
  · intro objId _ hTgt vtid hVal
    injection hTgt with hObj
    subst hObj
    simp only [validateThreadIdArg, SeLe4n.ThreadId.toValid?] at hVal
    rw [dif_neg (by decide)] at hVal
    cases hVal
    exact witnessThreadQuiescent

/-- **The suspend quiescence field is exercised under its own arm**: the
`.tcbSuspend` decode and the object target fire, and the field is proven of
the present witness thread. -/
theorem syscallDispatchQuiescence_inhabited_suspend :
    syscallDispatchQuiescence witnessDecodedSuspend witnessTid
      witnessGateSuspend witnessCapTcbObject witnessSt3 := by
  refine ⟨witnessReachable3, witnessCapOnlySuspend,
    ⟨witnessTcbBound, witnessSt3_getTcb, rfl, by simp [witnessTcbBound, witnessTcbFresh]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args hSy hDec
    simp [witnessDecodedSuspend] at hSy
  · intro epId hSy
    simp [witnessDecodedSuspend] at hSy
  · intro epId hSy
    simp [witnessDecodedSuspend] at hSy
  · intro epId hSy
    simp [witnessDecodedSuspend] at hSy
  · intro epId replyIdOpt hSy
    simp [witnessDecodedSuspend] at hSy
  · intro rid r callerTid hSy
    simp [witnessDecodedSuspend] at hSy
  · intro notifId hSy
    simp [witnessDecodedSuspend] at hSy
  · intro rid prevCaller replyBadge epId hSy
    simp [witnessDecodedSuspend] at hSy
  · intro rid r callerTid hSy hTgt hR hCaller
    simp [witnessDecodedSuspend] at hSy

end SeLe4n.Kernel
