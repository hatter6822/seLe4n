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
  signalStage : ∀ notifId badge, decoded.syscallId = .notificationSignal →
    cap.target = .object notifId →
    ∀ st1 res, notificationSignalOnCore notifId badge
        (determineExecutingCore st tid) st = (st1, res) →
    st1.objects.invExt
  waitReady : decoded.syscallId = .notificationWait →
    ∀ tcb : TCB, st.getTcb? tid = some tcb → tcb.ipcState = .ready
  waitStage : ∀ notifId, decoded.syscallId = .notificationWait →
    cap.target = .object notifId →
    ∀ st1 res, notificationWaitCrossCoreDispatch notifId tid st = (st1, res) →
    st1.objects.invExt
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
                      have hObjInv1 : st1.objects.invExt :=
                        hPack.signalStage notifId args.badge hSy hTgt st1 _ hSig
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
                      have hObjInv1 : st1.objects.invExt :=
                        hPack.waitStage notifId hSy hTgt st1 _ hWait
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

end SeLe4n.Kernel
