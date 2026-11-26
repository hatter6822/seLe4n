/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvBlockComposed
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvLegGuards
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeFrame

/-!
# The reply-receive whose receive leg takes a waiting sender, composed over its reply arm

WS-SX SX26.  A reply-receive whose receive leg meets a sender already queued
by a capability-free `Send` runs, whatever the reply's arm, the arm's reply leg
and pop (`ReplyRecvArm`, as the blocking receive runs them), the reply leg's
transfer, the server's context return on its bound notification, the take (the
sender popped, made ready and woken, the server handed its message), the arm's
deschedule of the server that gave its context back (seL4-MCS's
`reply_pop` on the donated arm leaves the server passive), and the server's
priority walk.  The arm's reply leg and pop are joined to the specification
once per arm (`ReplyRecvArm.legPop`), the take after them once for every arm
(`replyRecvAnsweringOnCore_take_of_pop`), so the take's shapes (the short and
the long message, the capability transfer, the fault answer) are each written
once over the arm.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

namespace ReplyRecvArm

/-- What the arm's pop hands back to the post-receive half: the donated arm
the context it returned and the server it took it from, every other arm
nothing. -/
@[inline] def returned : ReplyRecvArm → SeLe4n.SchedContextId → SeLe4n.ThreadId →
    Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)
  | .donated, scId, tid => some (scId, tid)
  | _, _, _ => none

/-- **What the arm's reply leg and pop ask of the pre-state**: the caller
blocked on the reply naming the server or none, the arm's pop guard, and the
popped context and the caller's home as the specification reads them.  The
receive leg's own checks are not here: the take and the block each add theirs. -/
def LegAdmits : ReplyRecvArm → SeLe4n.SchedContextId → CoreId → SystemState → SeLe4n.ThreadId →
    SeLe4n.ThreadId → SeLe4n.ReplyId → TCB → Prop
  | .rendezvous, _, _, st, tid, c, rid, ct =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid)) ∧
      replyWakesInPlace st c ct rid = true ∧ tid ≠ c
  | .donated, scId, home, st, tid, c, rid, ct =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid)) ∧ tid.isReserved = false ∧
      replyPopsInPlace st c ct.scBindingScCode tid rid = true ∧
      scId = ⟨replyHeadContextCode st rid - 1⟩ ∧ home = determineTargetCore st c
  | .held, scId, _, st, tid, c, rid, ct =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid)) ∧
      replyHeldPopsInPlace st c ct.scBindingScCode tid rid = true ∧
      scId = ⟨replyHeadContextCode st rid - 1⟩
  | .unheld, scId, home, st, tid, c, rid, ct =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 none) ∧
      replyUnheldPopsInPlace st c rid = true ∧ tid ≠ c ∧
      scId = ⟨replyHeadContextCode st rid - 1⟩ ∧ home = determineTargetCore st c
  | .unlinked, _, _, st, tid, c, rid, ct =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 none) ∧
      replyUnlinkedInPlace st c rid = true ∧ tid ≠ c

/-- **The arm's reply leg and pop are the specification's**, once per arm: the
reply leg answers the arm's reply writes, the pop hands back the arm's
`returned` on the arm's pop, and the recorded server the post-receive half
walks from is the server. -/
theorem legPop (arm : ReplyRecvArm) {scId : SeLe4n.SchedContextId} {home : CoreId}
    (st : SystemState) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (core : CoreId) (ct : TCB) (rp : Reply)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) :
    (recordedReplyServer? st c).getD tid = tid ∧ tid ≠ c ∧ st.objects.noResizeDue ∧
      st.objects.findsInPlace c.toObjId = true ∧
      ∃ S1 x, endpointReplyOnCore tid c msg core st = (S1, .ok x) ∧
        replyRecvPopDonation rid c S1 =
          .ok (arm.returned scId tid, arm.pop (arm.leg st c tid rid msg) c tid scId home) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  cases arm with
  | rendezvous =>
    obtain ⟨⟨ep0, hIpc⟩, hG, hNe⟩ := hAd
    have hFC : st.objects.findsInPlace c.toObjId = true := by
      simp only [replyWakesInPlace, Bool.and_eq_true] at hG
      exact hG.1.1.1.2
    obtain ⟨hEq, hHead⟩ := replyOnCore_inPlace st tid c tid ct ep0 rid msg core hSz hT hIpc hRO hG
    refine ⟨by simp only [recordedReplyServer?, hTc, hIpc, Option.getD_some], hNe,
      replyWakesInPlace_noResizeDue hG, hFC, _, _, hEq, ?_⟩
    unfold replyRecvPopDonation
    rw [replyFrameHeadHolder?_of_no_head _ _ hHead]
    simp only [popUnheldReplyHead_of_no_head _ _ _ _ hHead]
    rfl
  | donated =>
    obtain ⟨⟨ep0, hIpc⟩, hSRes, hG, rfl, rfl⟩ := hAd
    obtain ⟨rp', scId, sc, hRp', hN, _, _, _, hCode, hCRes, hNe, hNo, hLC, hFC, hLR, hFR,
      _, hPop⟩ := replyPopsInPlace_donation st c tid rid msg ct hT hSRes hG
    rw [hRp] at hRp'
    cases hRp'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
      rw [hCode]; rfl
    rw [hSc]
    obtain ⟨hEq, _⟩ := replyOnCore_eq_store st tid c tid ct ep0 rid rp msg core hSz hT hIpc hRO
      hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
    rw [← storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hPop
    exact ⟨by simp only [recordedReplyServer?, hTc, hIpc, Option.getD_some],
      fun e => hNe e.symm, hNo, hFC, _, _, hEq, hPop⟩
  | held =>
    obtain ⟨⟨ep0, hIpc⟩, hG, rfl⟩ := hAd
    obtain ⟨rp', scId, sc, _, hRp', hN, _, _, _, hCode, hCRes, _, hNe, hNo, _, _, hLC, hFC,
      hLR, hFR, _, hPop⟩ := replyHeldPopsInPlace_pop st c tid rid msg ct hT hG
    rw [hRp] at hRp'
    cases hRp'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
      rw [hCode]; rfl
    rw [hSc]
    obtain ⟨hEq, _⟩ := replyOnCore_eq_store st tid c tid ct ep0 rid rp msg core hSz hT hIpc hRO
      hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
    rw [← storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hPop
    exact ⟨by simp only [recordedReplyServer?, hTc, hIpc, Option.getD_some],
      fun e => hNe e.symm, hNo, hFC, _, _, hEq, hPop⟩
  | unheld =>
    obtain ⟨⟨ep0, hIpc⟩, hG, hNe, rfl, rfl⟩ := hAd
    obtain ⟨rp', scId, hRp', hN, hCode, hCRes, hNo, hLC, hFC, hLR, hFR, hPopR, -⟩ :=
      replyUnheldPopsInPlace_pop st c rid msg ct hT hG
    rw [hRp] at hRp'
    cases hRp'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
      rw [hCode]; rfl
    rw [hSc]
    obtain ⟨hEq, _⟩ := replyOnCore_eq_storeLeg st tid c none ct ep0 rid rp msg core hSz hT hIpc
      hRO hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
    simp only [SystemState.unlinkReplyWaiterOpt] at hEq
    rw [← storeReplyLeg_eq_hold _ _ _ _ hNo] at hPopR
    exact ⟨by simp only [recordedReplyServer?, hTc, hIpc, Option.getD_none], hNe, hNo, hFC,
      _, _, hEq, hPopR⟩
  | unlinked =>
    obtain ⟨⟨ep0, hIpc⟩, hG, hNe⟩ := hAd
    have hG' := hG
    simp only [replyUnlinkedInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG'
    obtain ⟨⟨⟨⟨⟨hCRes, hLC⟩, hFC⟩, hLR⟩, hFR⟩, hRpG⟩ := hG'
    rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRp] at hRpG
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hRpG
    obtain ⟨hNext, hPrev⟩ := hRpG
    obtain ⟨hEq, hR5⟩ := replyOnCore_eq_storeLeg st tid c none ct ep0 rid rp msg core hSz hT hIpc
      hRO hCRes hLC hFC hLR hFR hRp (Or.inl ⟨hNext, hPrev⟩)
    simp only [SystemState.unlinkReplyWaiterOpt] at hEq hR5
    have hHead : replyFrameHeadContext? (storeReplyLeg st c rid msg) rid = none := by
      unfold replyFrameHeadContext?
      rw [hR5]
      simp only [Reply.consumed, hNext]
    have hW : replyWakesInPlace st c ct rid = true := hG
    refine ⟨by simp only [recordedReplyServer?, hTc, hIpc, Option.getD_none], hNe,
      replyWakesInPlace_noResizeDue hW, hFC, _, _, hEq, ?_⟩
    unfold replyRecvPopDonation
    rw [replyFrameHeadHolder?_of_no_head _ _ hHead]
    simp only [popUnheldReplyHead_of_no_head _ _ _ _ hHead]
    rfl

/-- **The post-receive half after a take that dequeued no `Call`** is the arm's
deschedule and the server's priority walk: the donated arm's server, which
gave its context back, is taken off its core; every other arm keeps it. -/
theorem postReceive_noCall (arm : ReplyRecvArm) (scId : SeLe4n.SchedContextId)
    (tid s : SeLe4n.ThreadId) (core : CoreId) (X : SystemState)
    (h : rendezvousDequeuedCall X s = false) :
    replyRecvPostReceiveDonation tid tid s core (arm.returned scId tid) X =
      .ok ((), (PriorityInheritance.propagatePipChainCrossCore (arm.desched X tid) tid core).1) := by
  cases arm <;> simp [replyRecvPostReceiveDonation, returned, desched, h]

end ReplyRecvArm

/-- **The take after the arm's reply leg and pop is the specification's**, for
every arm and answer: once the reply leg answers `S1`, the pop hands back the
arm's `returned` on `P`, and the reply leg's transfer answers `(summary, S2)`,
a sender `s` at the head of the send queue on the state the server's context
return leaves, blocked by a routed capability-free send and not delivering a
fault, whose take writes only its slots, is taken (`receiveTake_delivered`);
the arm's deschedule and the server's priority walk follow, then the caller's
answer. -/
theorem replyRecvAnsweringOnCore_take_of_pop (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} (answer : Option Architecture.FaultReplyOutcome)
    (st : SystemState) (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (msg : IpcMessage) (grant : Bool) (core : CoreId) (ep : Endpoint) (s : SeLe4n.ThreadId)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo) {S1 P : SystemState} {x : Option (CoreId × SgiKind)}
    (hRecS : (recordedReplyServer? st c).getD tid = tid)
    (hEq : endpointReplyOnCore tid c msg core st = (S1, .ok x))
    (hPop : replyRecvPopDonation rid c S1 = .ok (arm.returned scId tid, P))
    (hH : ep.sendQ.head = some s)
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyRecvReplyTransfer answer st tid c grant P = .ok (summary, S2))
    (hE2 : (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep))
    {sTcb2 : TCB}
    (hT2 : (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2))
    (hG2 : receiveTakesInPlace (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 =
          .send capAddr mi)
    (hF : sTcb2.ipcFaultSend = false) :
    endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
      .ok ({ results := #[] }, replyRecvAnswerCaller answer
        (PriorityInheritance.propagatePipChainCrossCore (arm.desched
          ((wakeThread ((storePopHead (receiveReturnSchedContext true S2 tid) epId false s
              sTcb2.queueNext).updateTcb s receiverReady) s core).1.updateTcb tid
            (callReceiverTcb (blockedSenderMessage (storePopHead
              (receiveReturnSchedContext true S2 tid) epId false s sTcb2.queueNext) s sTcb2))) tid)
          tid core).1 c summary.capInfo) := by
  generalize hQ : receiveReturnSchedContext true S2 tid = Q at hE2 hT2 hG2 ⊢
  obtain ⟨hRecv, -, -⟩ := receiveTake_delivered Q epId ep tid (some rid) core s sTcb2 capAddr mi
    hE2 hH hT2 hG2 hR hF
  have hNoCall := receiveTake_dequeuedNoCall Q epId ep tid core s sTcb2
    (blockedSenderMessage (storePopHead Q epId false s sTcb2.queueNext) s sTcb2) hE2 hH hT2 hG2
  unfold endpointReplyRecvAnsweringOnCore
  simp only [hRecS, hEq, hPop, hXf, hQ, hRecv,
    ReplyRecvArm.postReceive_noCall arm scId tid s core _ hNoCall]
  simp [applyReceiveLegPipHandoff]

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- **The reply leg and the arm's pop carry the take's guard**: on the state
they leave, the endpoint is as it was, the sender `s` is a thread keeping every
word the take reads, and the take's in-place guard, read on the pre-state,
still holds.  Per arm, the arm's own carry (`storeReplyRendezvous_takeGuard`,
`popDonationSettled_takeGuard`, `keepHeldPop_takeGuard`,
`popUnheldSettled_takeGuard`, `storeReplyLeg_takeGuard`). -/
theorem ReplyRecvArm.takeGuard (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c) (hST : s ≠ tid)
    (hG : receiveTakesInPlace st epId tid s sTcb = true) :
    (arm.pop (arm.leg st c tid rid msg) c tid scId home).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (arm.pop (arm.leg st c tid rid msg) c tid scId home).objects[s.toObjId]? =
          some (.tcb sTcb1) ∧ SenderWordsKept sTcb1 sTcb ∧
        receiveTakesInPlace (arm.pop (arm.leg st c tid rid msg) c tid scId home) epId tid s sTcb1 =
          true := by
  cases arm with
  | rendezvous =>
    exact storeReplyRendezvous_takeGuard st c tid rid msg ct rp epId ep s sTcb hNo hT hFC hRp hE
      hS hSC hG
  | donated =>
    exact popDonationSettled_takeGuard st c tid rid msg ct rp scId home epId ep s sTcb hNo hT hFC
      hRp hE hS hSC hST hG
  | held =>
    exact keepHeldPop_takeGuard st c tid rid msg ct rp scId epId ep s sTcb hNo hT hFC hRp hE hS hSC
      hST hG
  | unheld =>
    exact popUnheldSettled_takeGuard st c tid rid msg ct rp scId home epId ep s sTcb hNo hT hFC hRp
      hE hS hSC hG
  | unlinked =>
    exact storeReplyLeg_takeGuard st c tid rid msg ct rp epId ep s sTcb hNo hT hFC hRp hE hS hSC hG

/-- **The reply-receive meeting a waiting sender, over every arm and answer**:
under the arm's reply-leg guard, a sender `s` at the head of the endpoint's
send queue, blocked by a routed capability-free send, not delivering a fault,
whose take writes only its slots (each read on the pre-state), and a reply-leg
transfer answering `(summary, S2)` within the transfer's frame, the composite
is the arm's reply leg and pop, the transfer, the server's context return, the
take, the arm's deschedule and the server's priority walk, then the caller's
answer; the sender on the state the return leaves keeps every word the take
reads.  The one equality every take shape is joined to the specification
through: the reply leg and pop per arm (`ReplyRecvArm.legPop`), the take once
(`replyRecvAnsweringOnCore_take_of_pop`). -/
theorem replyRecvAnsweringOnCore_arm_take (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId}
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
          .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false)
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyRecvReplyTransfer answer st tid c grant
      (arm.pop (arm.leg st c tid rid msg) c tid scId home) = .ok (summary, S2))
    (hFr : transferFrame S2 (arm.pop (arm.leg st c tid rid msg) c tid scId home))
    (hNo2 : S2.objects.noResizeDue) :
    ∃ sTcb2, (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep) ∧
      (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2) ∧
      SenderWordsKept sTcb2 sTcb ∧
      receiveTakesInPlace (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 = true ∧
      endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
        .ok ({ results := #[] }, replyRecvAnswerCaller answer
          (PriorityInheritance.propagatePipChainCrossCore (arm.desched
            ((wakeThread ((storePopHead (receiveReturnSchedContext true S2 tid) epId false s
                sTcb2.queueNext).updateTcb s receiverReady) s core).1.updateTcb tid
              (callReceiverTcb (blockedSenderMessage (storePopHead
                (receiveReturnSchedContext true S2 tid) epId false s sTcb2.queueNext) s sTcb2)))
              tid) tid core).1 c summary.capInfo) := by
  obtain ⟨hRecS, hNe, hNo, hFC, S1, x, hEq, hPop⟩ :=
    arm.legPop (scId := scId) (home := home) st tid c rid msg core ct rp hAd hSz hT hRO hRp
  have hST : s ≠ tid := by
    have h := hGt
    simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    exact fun e => h.1.1.1.1.1.2 e.symm
  obtain ⟨hE1, sTcb1, hS1, hK1, hG1⟩ := arm.takeGuard (scId := scId) (home := home) st c tid rid
    msg ct rp epId ep s sTcb hNo hT hFC hRp hE hS hSC hST hGt
  obtain ⟨hE2', sTcb2', hS2', hK2', hG2'⟩ := takeGuard_of_transferFrame hFr hE1 hS1 hG1
  obtain ⟨hE2, sTcb2, hS2, hK2, hG2⟩ := receiveReturnSchedContext_takeGuard true S2 tid hNo2 hE2'
    hS2' hG2'
  have hK := hK2.trans (hK2'.trans hK1)
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 =
          .send capAddr mi := by rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  exact ⟨sTcb2, hE2, hS2, hK, hG2, replyRecvAnsweringOnCore_take_of_pop arm answer st epId tid c
    rid msg grant core ep s capAddr mi hRecS hEq hPop hH hXf hE2 hS2 hG2 hR2 hF2⟩

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- **The take's writes before the server's own frame, over the arm**: the
sender popped, made ready and woken, the server made ready, the arm's
deschedule, the server's priority walk, then the caller's frame with the
transfer's report (read from the server's saved registers `rf`). -/
@[inline] def ReplyRecvArm.takeLegs (arm : ReplyRecvArm) (capInfo : Nat) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (nextCode : Nat) (core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) : SystemState :=
  let W := (wakeThread ((storePopHead Y epId false s (ThreadId.ofOptCode nextCode)).updateTcb s
    receiverReady) s core).1
  let Z := (PriorityInheritance.propagatePipChainCrossCore (arm.desched (W.updateTcb tid
    receiverReady) tid) tid core).1
  deliverReplyRecvCapsFrame capInfo Z c layout rf len badge

/-- The arm's deschedule commutes with a held message. -/
theorem ReplyRecvArm.desched_hold (arm : ReplyRecvArm) (r : SeLe4n.ThreadId) (m : IpcMessage)
    (X : SystemState) (tid : SeLe4n.ThreadId) :
    arm.desched (X.mapTcbInPlace r (holdMessage m)) tid =
      (arm.desched X tid).mapTcbInPlace r (holdMessage m) :=
  arm.desched_msg r id (fun _ => some m) id X tid

/-- **The take's tail, over the arm, stages the caller's held reply and the
server's message as frames**, the arm's deschedule committed past both
writes (`ReplyRecvArm.desched_hold`). -/
theorem ReplyRecvArm.takeFrame_staged (arm : ReplyRecvArm) (Y : SystemState) (c tid s : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (sTcb : TCB) (core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (capInfo : Nat) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hNo : Y.objects.noResizeDue) (hNe : tid ≠ c) (hSC : s ≠ c)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hE : (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regMessageBody layout rf len, badge := badge })).objects[epId]? =
        some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regMessageBody layout rf len, badge := badge })).objects[s.toObjId]? =
        some (.tcb sTcb))
    (hG : receiveTakesInPlace (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regMessageBody layout rf len, badge := badge })) epId tid s sTcb
        = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
          (PriorityInheritance.propagatePipChainCrossCore (arm.desched
            ((wakeThread ((storePopHead (Y.mapTcbInPlace c (holdMessage
                { registers := Architecture.regMessageBody layout rf len, badge := badge }))
                epId false s sTcb.queueNext).updateTcb s receiverReady) s core).1.updateTcb tid
              (callReceiverTcb (blockedSenderMessage (storePopHead (Y.mapTcbInPlace c (holdMessage
                { registers := Architecture.regMessageBody layout rf len, badge := badge }))
                epId false s sTcb.queueNext) s sTcb))) tid) tid core).1 c capInfo) tid 0 =
      writeTakerFrame
        (arm.takeLegs capInfo Y c tid s epId sTcb.queueNextCode core layout rf len badge) tid
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5 := by
  generalize hM : ({ registers := Architecture.regMessageBody layout rf len, badge := badge } :
    IpcMessage) = m at hE hT hG
  generalize hS2 : Y.mapTcbInPlace c (holdMessage m) = S2 at hE hT hG
  have hG' := hG
  simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, _⟩, hRS⟩, hRN⟩, _⟩, _⟩, hRT⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hFH⟩, _⟩ := hSG'
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : epId ≠ tid.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ tid.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ tid.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨_, hFr⟩ := popHead_inPlace S2 epId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace
    ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady)
    (determineTargetCore ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady) s)
    s _ hT2s rfl (by rw [updateTcb_findsInPlace _ hFr.head_tcb hFH1]; exact hFH1)
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1 hNeSR).trans hO1r
  obtain ⟨rt3, hO3r, _⟩ := hA3.get_tcb hO2r
  have hW3r : (wakeThread ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady)
      s core).1.getTcb? tid = some rt3 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  have hMsg := (blockedSender_of_routedSend (storePopHead S2 epId false s sTcb.queueNext) s sTcb
    capAddr mi hR hF).2
  generalize blockedSenderMessage (storePopHead S2 epId false s sTcb.queueNext) s sTcb = msgS
    at hMsg
  subst hS2
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have hST : s ≠ tid := fun e => hRS e.symm
  have hNoPY := storePopHead_noResizeDue Y epId false s sTcb.queueNext hNo
  have hNoU := updateTcb_noResizeDue _ s receiverReady hNoPY
  have hNoWY := wakeThread_noResizeDue _ s core hNoU
  have hNoWr := updateTcb_noResizeDue _ tid receiverReady hNoWY
  have hNoDs := arm.desched_noResizeDue _ tid hNoWr
  have hNoZ := propagatePipChainCrossCore_noResizeDue _ tid core hNoDs
  have hNoZs : (SystemState.mapTcbInPlace (PriorityInheritance.propagatePipChainCrossCore
      (arm.desched ((wakeThread ((storePopHead Y epId false s sTcb.queueNext).updateTcb s
        receiverReady) s core).1.updateTcb tid receiverReady) tid) tid core).1 tid
        (holdMessage msgS)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoZ
  have hNoD := deliverReplyRecvCapsFrame_noResizeDue capInfo _ c layout rf len badge hNoZ
  rw [storePopHead_msg c _ _ _ Y epId false s sTcb.queueNext hNo] at hW3r ⊢
  rw [updateTcb_msg c _ _ _ _ s receiverReady hNoPY (fun h => absurd h hSC)] at hW3r ⊢
  rw [wakeThread_msg c _ _ _ _ s core hNoU] at hW3r ⊢
  dsimp only at hW3r ⊢
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hW3r
  unfold writeTakerFrame ReplyRecvArm.takeLegs
  dsimp only
  rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode]
  generalize (wakeThread ((storePopHead Y epId false s sTcb.queueNext).updateTcb s receiverReady) s
    core).1 = W at hW3r hNoWY hNoWr hNoDs hNoZ hNoZs hNoD ⊢
  have hNoWrc : ((W.updateTcb tid receiverReady).mapTcbInPlace c (holdMessage m)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoWr
  rw [updateTcb_msg c _ _ _ _ tid (callReceiverTcb msgS) hNoWY (fun h => absurd h hNe),
    SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, ← holdMessage_receiverReady,
    ← SystemState.mapTcbInPlace_mapTcbInPlace, ← SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY,
    SystemState.mapTcbInPlace_swap _ (holdMessage msgS) (holdMessage m)
      (fun h => absurd h (fun e => hNe e.symm)),
    arm.desched_hold, propagatePipChainCrossCore_msg _ _ _ _ _ _ _
      (arm.desched_noResizeDue _ tid hNoWrc),
    arm.desched_hold, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoDs,
    SystemState.mapTcbInPlace_swap _ (holdMessage m) (holdMessage msgS) (fun h => absurd h hNe),
    stageDeliveredMessage_holdMessage_caps _ _ _ _ hNoZs
      (by rw [← hM, Architecture.regMessageBody_size]; exact hSz4),
    writeDeliveredFrameIfReady_mapTcbInPlace _ c tid _ _ _ (fun e => hNe e.symm),
    ← hM, returnFrameOfMessage_regMessageBody_capsOpt]
  have hWr : (W.updateTcb tid receiverReady).getTcb? tid = some (receiverReady rt3) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, SystemState.mapTcbInPlace_getTcb?_self,
      hW3r]; rfl
  obtain ⟨x1, hX1, hX1s⟩ := arm.desched_ipcStateCarried _ tid tid _ hWr
  obtain ⟨x, hX, hX2s⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core hNoDs tid _ hX1
  have hXs := hX2s.trans hX1s
  generalize (PriorityInheritance.propagatePipChainCrossCore (arm.desched (W.updateTcb tid
    receiverReady) tid) tid core).1 = Z at hX hNoZ hNoZs hNoD ⊢
  rw [show writeDeliveredFrameIfReady Z c (regMessageFrameCapsOpt layout rf len badge capInfo)
      (fun _ => Z.mapTcbInPlace c (holdMessage
        { registers := Architecture.regMessageBody layout rf len, badge := badge })) =
      deliverReplyRecvCapsFrame capInfo Z c layout rf len badge from rfl]
  have hDr := (deliverReplyRecvCapsFrame_getTcb?_ne capInfo Z c tid layout rf len badge hCT).trans hX
  generalize deliverReplyRecvCapsFrame capInfo Z c layout rf len badge = D at hDr hNoD ⊢
  have hSzS : msgS.registers.size ≤ 4 := by
    rw [hMsg]
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [stageDeliveredMessage_holdMessage _ _ _ hNoD hSzS, hMsg,
    Architecture.returnFrameOfMessage_regMessageBody]
  unfold writeDeliveredFrameIfReady
  rw [hDr]
  dsimp only
  rw [if_pos (by rw [hXs]; rfl)]

/-- The arm's reply leg and pop, the caller then holding `msg`, are the arm's
writes with the caller woken holding nothing, the message then held. -/
theorem ReplyRecvArm.pop_leg_hold (arm : ReplyRecvArm) {scId : SeLe4n.SchedContextId}
    {home : CoreId} (st : SystemState) (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (msg : IpcMessage) (hNo : st.objects.noResizeDue) (hNe : tid ≠ c) :
    arm.pop (arm.leg st c tid rid msg) c tid scId home =
      (arm.pop (arm.legReady st c tid rid) c tid scId home).mapTcbInPlace c (holdMessage msg) := by
  rw [arm.leg_eq_hold st c tid rid msg hNo]
  exact arm.pop_msg (scId := scId) (home := home) c id (fun _ => some msg) id _ c tid
    (arm.legReady_noResizeDue st c tid rid hNo) (fun e => hNe e.symm)

/-- **The reply-receive meeting a waiting sender, over every arm, its reply
transferring nothing, delivered**: the arm's reply leg and pop, the server's
context return, the take, the arm's deschedule, the server's priority walk and
the caller's frame (`ReplyRecvArm.takeLegs`). -/
@[noinline] def performReplyRecvArmTakeLegs (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) : SystemState :=
  arm.takeLegs 0 (receiveReturnSchedContextFast true
    (arm.pop (arm.legReady st c tid rid) c tid scId home) tid.val) c tid s epId nextCode core
    layout rf len badge

/-- The inert take over the arm, the legs (`performReplyRecvArmTakeLegs`) and
then the server's frame (`writeTakerFrame`), each out of line so the arm
releases the server's register file between them. -/
@[inline] def performReplyRecvArmTakeDelivered (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  writeTakerFrame (performReplyRecvArmTakeLegs arm scId home st c tid rid epId s nextCode core
    layout rf len badge) tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive meeting a waiting sender, its reply transferring
nothing, is the specification's, over every arm**: under the arm's reply-leg
guard, a reply of at most four words transferring no capability, and a sender
`s` at the head of the send queue blocked by a routed capability-free send, not
delivering a fault, whose take writes only its slots (every check read on the
pre-state), the checked arm's result is `performReplyRecvArmTakeDelivered`. -/
theorem replyRecvOnCore_arm_takeDelivered (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hInert : replyTransferInert st tid ct grant = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
          .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmTakeDelivered arm scId home st c tid rid epId s
        sTcb.queueNextCode core layout rf len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5) := by
  have hSz : ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regMessageBody_size]; unfold maxMessageRegisters; omega
  obtain ⟨-, hNe, hNo, -, -⟩ :=
    arm.legPop (scId := scId) (home := home) st tid c rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge } core ct rp hAd
      hSz hT hRO hRp
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNoX := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid
    (arm.legReady_noResizeDue st c tid rid hNo)
  have hNoP : (arm.pop (arm.leg st c tid rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge }) c tid scId
      home).objects.noResizeDue := by
    rw [arm.pop_leg_hold st c tid rid _ hNo hNe]
    exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoX
  have hXf := replyRecvReplyTransfer_of_inert none st tid c grant ct hTc (fun _ => hInert)
    (arm.pop (arm.leg st c tid rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge }) c tid scId home)
  obtain ⟨sTcb2, hE2, hS2, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_take arm none st epId
    tid c rid _ grant core ct rp ep s sTcb capAddr mi hAd hSz hT hRO hRp hE hH hS hSC hGt hR hF hXf
    (transferFrame.refl _) hNoP
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 =
          .send capAddr mi := by rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  unfold endpointReplyRecvOnCore
  rw [hEq]
  dsimp only
  rw [CapTransferSummary.capInfo_empty, replyRecvAnswerCaller_none]
  rw [arm.pop_leg_hold st c tid rid _ hNo hNe,
    receiveReturnSchedContext_msg c id _ id true _ tid hNoX hNe.symm] at hE2 hS2 hG2 ⊢
  rw [arm.takeFrame_staged _ c tid s epId ep sTcb2 core layout rf len badge 0 capAddr mi
    (receiveReturnSchedContext_noResizeDue true _ tid hNoX) hNe hSC hSz4 hE2 hH hS2 hG2 hR2 hF2,
    hK.queueNext, hK.regs, hK.ipcBadgeView]
  unfold performReplyRecvArmTakeDelivered performReplyRecvArmTakeLegs
  rw [receiveReturnSchedContextFast_eq]

/-- **The reply-receive meeting a waiting sender, over every arm, its reply
leg transferring, delivered**: the arm's reply leg and pop, the transfer in
place on no endpoint, the server's context return, the take, the arm's
deschedule, the server's priority walk, then the caller's frame with the
transfer's report.  The replier and the caller enter as the words the transfer
reads of them, all read before the reply's writes. -/
@[noinline] def performReplyRecvArmTakeCapsLegs (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := arm.pop (arm.legReady st c tid rid) c tid scId home
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    arm.takeLegs (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (receiveReturnSchedContextFast true
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X) tid.val)
      c tid s epId nextCode core layout rf len badge

/-- The installing take over the arm, its legs (`performReplyRecvArmTakeCapsLegs`)
and then the server's frame (`writeTakerFrame`). -/
@[inline] def performReplyRecvArmTakeCapsDelivered (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (w0 w1 w2 w3 w4 w5 : UInt64)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  writeTakerFrame (performReplyRecvArmTakeCapsLegs arm scId home st c tid rid epId s nextCode core
    layout rf len badge sv sb sroot count rv rb rroot) tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive meeting a waiting sender, its reply leg transferring,
is the specification's, over every arm**: under the guard of
`replyRecvOnCore_arm_takeDelivered` (its inert transfer replaced by a granting
replier whose frame asks for `count` capabilities, `hReq`), the checked arm's
result is `performReplyRecvArmTakeCapsDelivered`. -/
theorem replyRecvOnCore_arm_takeCapsDelivered (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (stcb : TCB) (count : Nat)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
          .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmTakeCapsDelivered arm scId home st c tid rid epId s
        sTcb.queueNextCode core layout rf len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5
        stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] count ct.spaceCells[2] ct.ipcBuffer
        ct.spaceCells[0]) := by
  have hSz : ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regMessageBody_size]; unfold maxMessageRegisters; omega
  obtain ⟨-, hNe, hNo, -, -⟩ :=
    arm.legPop (scId := scId) (home := home) st tid c rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge } core ct rp hAd
      hSz hT hRO hRp
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  have hP1 := arm.pop_leg_hold (scId := scId) (home := home) st c tid rid
    { registers := Architecture.regMessageBody layout rf len, badge := badge } hNo hNe
  have hNoX := arm.legReady_noResizeDue st c tid rid hNo
  have hAP := (arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid hNoX).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid hNoX
  generalize hX : arm.pop (arm.legReady st c tid rid) c tid scId home = X at hP1 hNoP hAP
  generalize hMsg : ({ registers := Architecture.regMessageBody layout rf len, badge := badge } :
    IpcMessage) = msg at hP1
  obtain ⟨sm, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 sm hNoP hT1
  have hHT : receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
      (X.mapTcbInPlace c (holdMessage msg)) = .ok (sm, Y1.mapTcbInPlace c (holdMessage msg)) := by
    rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoP, hT1]
    rfl
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAP)
    ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoP) c.toObjId stcb ct count hHT).1
  have hXf : replyRecvReplyTransfer none st tid c true
      (arm.pop (arm.leg st c tid rid msg) c tid scId home) =
      .ok (sm, Y1.mapTcbInPlace c (holdMessage msg)) := by
    show replyTransferCaps st tid c true _ = _
    unfold replyTransferCaps
    rw [hReq, hTgt, hP1, hHT]
  rw [← hP1] at hFr
  subst hMsg
  obtain ⟨sTcb2, hE2, hS2, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_take arm none st epId
    tid c rid _ true core ct rp ep s sTcb capAddr mi hAd hSz hT hRO hRp hE hH hS hSC hGt hR hF hXf
    hFr ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoY)
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 =
          .send capAddr mi := by rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  unfold endpointReplyRecvOnCore
  rw [hEq]
  dsimp only
  rw [CapTransferSummary.capInfo_empty, replyRecvAnswerCaller_none]
  rw [receiveReturnSchedContext_msg c id _ id true Y1 tid hNoY hNe.symm] at hE2 hS2 hG2 ⊢
  rw [arm.takeFrame_staged _ c tid s epId ep sTcb2 core layout rf len badge sm.capInfo capAddr mi
    (receiveReturnSchedContext_noResizeDue true Y1 tid hNoY) hNe hSC hSz4 hE2 hH hS2 hG2 hR2 hF2,
    hK.queueNext, hK.regs, hK.ipcBadgeView, ← receiveReturnSchedContextFast_eq]
  have hKl := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => arm.takeLegs i (receiveReturnSchedContextFast true Y tid.val) c tid s epId
      sTcb.queueNextCode core layout rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hKl
  rw [hAP.frameCapRequestOf, hAP.capTargetOf, hT1] at hKl
  unfold performReplyRecvArmTakeCapsDelivered performReplyRecvArmTakeCapsLegs
  rw [hX]
  dsimp only
  rw [hKl]

/-! ### The long message -/

/-- **The long take's writes before the server's own frame, over the arm**:
as `ReplyRecvArm.takeLegs`, the caller's long frame with the replier's
overflow words copied into its buffer (`deliverLongReplyRecvFrame`). -/
@[inline] def ReplyRecvArm.takeLegsLong (arm : ReplyRecvArm) (capInfo : Nat) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (nextCode : Nat) (core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) : SystemState :=
  let W := (wakeThread ((storePopHead Y epId false s (ThreadId.ofOptCode nextCode)).updateTcb s
    receiverReady) s core).1
  let Z := (PriorityInheritance.propagatePipChainCrossCore (arm.desched (W.updateTcb tid
    receiverReady) tid) tid core).1
  deliverLongReplyRecvFrame Z c rf len tid badge capInfo

/-- **The long take's tail, over the arm**, stages the caller's held reply and
the server's message as frames, the arm's deschedule committed past both
writes (`ReplyRecvArm.desched_hold`). -/
theorem ReplyRecvArm.takeFrame_stagedLong (arm : ReplyRecvArm) (st0 Y : SystemState) (c tid s : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (sTcb : TCB) (core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (capInfo : Nat) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hNo : Y.objects.noResizeDue) (hAY : ipcWordReadsAgree Y st0) (hNe : tid ≠ c) (hSC : s ≠ c)
    (hLen : 4 ≤ len)
    (hE : (Y.mapTcbInPlace c (holdMessage
      { registers := longReplyRecvRegs rf st0 tid len, badge := badge })).objects[epId]? =
        some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : (Y.mapTcbInPlace c (holdMessage
      { registers := longReplyRecvRegs rf st0 tid len, badge := badge })).objects[s.toObjId]? =
        some (.tcb sTcb))
    (hG : receiveTakesInPlace (Y.mapTcbInPlace c (holdMessage
      { registers := longReplyRecvRegs rf st0 tid len, badge := badge })) epId tid s sTcb
        = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
          (PriorityInheritance.propagatePipChainCrossCore (arm.desched
            ((wakeThread ((storePopHead (Y.mapTcbInPlace c (holdMessage
                { registers := longReplyRecvRegs rf st0 tid len, badge := badge }))
                epId false s sTcb.queueNext).updateTcb s receiverReady) s core).1.updateTcb tid
              (callReceiverTcb (blockedSenderMessage (storePopHead (Y.mapTcbInPlace c (holdMessage
                { registers := longReplyRecvRegs rf st0 tid len, badge := badge }))
                epId false s sTcb.queueNext) s sTcb))) tid) tid core).1 c capInfo) tid 0 =
      writeTakerFrame
        (arm.takeLegsLong capInfo Y c tid s epId sTcb.queueNextCode core rf len badge) tid
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5 := by
  generalize hM : ({ registers := longReplyRecvRegs rf st0 tid len, badge := badge } :
    IpcMessage) = m at hE hT hG
  generalize hS2 : Y.mapTcbInPlace c (holdMessage m) = S2 at hE hT hG
  have hG' := hG
  simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, _⟩, hRS⟩, hRN⟩, _⟩, _⟩, hRT⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hFH⟩, _⟩ := hSG'
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : epId ≠ tid.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ tid.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ tid.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨_, hFr⟩ := popHead_inPlace S2 epId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace
    ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady)
    (determineTargetCore ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady) s)
    s _ hT2s rfl (by rw [updateTcb_findsInPlace _ hFr.head_tcb hFH1]; exact hFH1)
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1 hNeSR).trans hO1r
  obtain ⟨rt3, hO3r, _⟩ := hA3.get_tcb hO2r
  have hW3r : (wakeThread ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady)
      s core).1.getTcb? tid = some rt3 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  have hMsg := (blockedSender_of_routedSend (storePopHead S2 epId false s sTcb.queueNext) s sTcb
    capAddr mi hR hF).2
  generalize blockedSenderMessage (storePopHead S2 epId false s sTcb.queueNext) s sTcb = msgS
    at hMsg
  subst hS2
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have hST : s ≠ tid := fun e => hRS e.symm
  have hNoPY := storePopHead_noResizeDue Y epId false s sTcb.queueNext hNo
  have hNoU := updateTcb_noResizeDue _ s receiverReady hNoPY
  have hNoWY := wakeThread_noResizeDue _ s core hNoU
  have hNoWr := updateTcb_noResizeDue _ tid receiverReady hNoWY
  have hNoDs := arm.desched_noResizeDue _ tid hNoWr
  have hNoZ := propagatePipChainCrossCore_noResizeDue _ tid core hNoDs
  have hNoZs : (SystemState.mapTcbInPlace (PriorityInheritance.propagatePipChainCrossCore
      (arm.desched ((wakeThread ((storePopHead Y epId false s sTcb.queueNext).updateTcb s
        receiverReady) s core).1.updateTcb tid receiverReady) tid) tid core).1 tid
        (holdMessage msgS)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoZ
  rw [storePopHead_msg c _ _ _ Y epId false s sTcb.queueNext hNo] at hW3r ⊢
  rw [updateTcb_msg c _ _ _ _ s receiverReady hNoPY (fun h => absurd h hSC)] at hW3r ⊢
  rw [wakeThread_msg c _ _ _ _ s core hNoU] at hW3r ⊢
  dsimp only at hW3r ⊢
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hW3r
  unfold writeTakerFrame ReplyRecvArm.takeLegsLong
  dsimp only
  rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode]
  have hAW : ipcWordReadsAgree (wakeThread ((storePopHead Y epId false s sTcb.queueNext).updateTcb
      s receiverReady) s core).1 st0 :=
    ((ipcBufferReadsAgree_wakeThread _ s core hNoU).trans
      ((ipcBufferReadsAgree_updateTcb _ s receiverReady (fun _ => ⟨rfl, rfl⟩) hNoPY).trans
        (ipcBufferReadsAgree_storePopHead Y epId false s sTcb.queueNext hNo))).words.trans hAY
  generalize (wakeThread ((storePopHead Y epId false s sTcb.queueNext).updateTcb s receiverReady) s
    core).1 = W at hW3r hNoWY hNoWr hNoDs hNoZ hNoZs hAW ⊢
  have hNoWrc : ((W.updateTcb tid receiverReady).mapTcbInPlace c (holdMessage m)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoWr
  rw [updateTcb_msg c _ _ _ _ tid (callReceiverTcb msgS) hNoWY (fun h => absurd h hNe),
    SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, ← holdMessage_receiverReady,
    ← SystemState.mapTcbInPlace_mapTcbInPlace, ← SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY,
    SystemState.mapTcbInPlace_swap _ (holdMessage msgS) (holdMessage m)
      (fun h => absurd h (fun e => hNe e.symm)),
    arm.desched_hold, propagatePipChainCrossCore_msg _ _ _ _ _ _ _
      (arm.desched_noResizeDue _ tid hNoWrc),
    arm.desched_hold, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoDs,
    SystemState.mapTcbInPlace_swap _ (holdMessage m) (holdMessage msgS) (fun h => absurd h hNe)]
  have hAZ : ipcWordReadsAgree (PriorityInheritance.propagatePipChainCrossCore
      (arm.desched (W.updateTcb tid receiverReady) tid) tid core).1 st0 :=
    ((ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core hNoDs).trans
      ((arm.ipcBufferReadsAgree_desched _ tid).trans (ipcBufferReadsAgree_updateTcb _ tid receiverReady (fun _ => ⟨rfl, rfl⟩) hNoWY))).words.trans
      hAW
  have hAZs := (ipcBufferReadsAgree_mapTcbInPlace _ tid (holdMessage msgS)
    (fun _ => ⟨rfl, rfl⟩)).words.trans hAZ
  rw [← hM, ← deliverLongReplyRecvFrame_eq _ st0 c tid rf len badge capInfo hNoZs hAZs hLen,
    deliverLongReplyRecvFrame_mapTcbInPlace _ c tid tid rf len badge capInfo (holdMessage msgS)
      (fun _ => ⟨rfl, rfl⟩) (fun e => hNe e.symm)]
  have hWr : (W.updateTcb tid receiverReady).getTcb? tid = some (receiverReady rt3) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, SystemState.mapTcbInPlace_getTcb?_self,
      hW3r]; rfl
  obtain ⟨x1, hX1, hX1s⟩ := arm.desched_ipcStateCarried _ tid tid _ hWr
  obtain ⟨x, hX, hX2s⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core hNoDs tid _ hX1
  have hXs := hX2s.trans hX1s
  generalize (PriorityInheritance.propagatePipChainCrossCore (arm.desched (W.updateTcb tid
    receiverReady) tid) tid core).1 = Z at hX hNoZ hNoZs hAZ hAZs ⊢
  have hNoD := deliverLongReplyRecvFrame_noResizeDue Z c rf len tid badge capInfo hNoZ
  have hDr := (deliverLongReplyRecvFrame_getTcb?_ne Z c tid tid rf len badge capInfo hCT).trans hX
  generalize deliverLongReplyRecvFrame Z c rf len tid badge capInfo = D at hDr hNoD ⊢
  have hSzS : msgS.registers.size ≤ 4 := by
    rw [hMsg]
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [stageDeliveredMessage_holdMessage _ _ _ hNoD hSzS, hMsg,
    Architecture.returnFrameOfMessage_regMessageBody]
  unfold writeDeliveredFrameIfReady
  rw [hDr]
  dsimp only
  rw [if_pos (by rw [hXs]; rfl)]

/-- **The reply-receive meeting a waiting sender, over every arm, its reply
transferring nothing, delivered, at more than four words**: the arm's reply leg and pop, the server's
context return, the take, the arm's deschedule, the server's priority walk and
the caller's frame (`ReplyRecvArm.takeLegsLong`). -/
@[noinline] def performReplyRecvArmTakeLegsLong (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) : SystemState :=
  arm.takeLegsLong 0 (receiveReturnSchedContextFast true
    (arm.pop (arm.legReady st c tid rid) c tid scId home) tid.val) c tid s epId nextCode core
    rf len badge

/-- The inert take over the arm, the legs (`performReplyRecvArmTakeLegsLong`) and
then the server's frame (`writeTakerFrame`), each out of line so the arm
releases the server's register file between them. -/
@[inline] def performReplyRecvArmTakeDeliveredLong (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  writeTakerFrame (performReplyRecvArmTakeLegsLong arm scId home st c tid rid epId s nextCode core
    rf len badge) tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive meeting a waiting sender, its reply transferring
nothing, is the specification's, over every arm**: under the arm's reply-leg
guard, a reply of at most four words transferring no capability, and a sender
`s` at the head of the send queue blocked by a routed capability-free send, not
delivering a fault, whose take writes only its slots (every check read on the
pre-state), the checked arm's result is `performReplyRecvArmTakeDeliveredLong`. -/
theorem replyRecvOnCore_arm_takeDeliveredLong (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hLen : 5 ≤ len)
    (hSzL : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hInert : replyTransferInert st tid ct grant = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
          .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmTakeDeliveredLong arm scId home st c tid rid epId s
        sTcb.queueNextCode core rf len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5) := by
  have hSz := hSzL
  obtain ⟨-, hNe, hNo, -, -⟩ :=
    arm.legPop (scId := scId) (home := home) st tid c rid
      { registers := longReplyRecvRegs rf st tid len, badge := badge } core ct rp hAd
      hSz hT hRO hRp
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNoX := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid
    (arm.legReady_noResizeDue st c tid rid hNo)
  have hNoP : (arm.pop (arm.leg st c tid rid
      { registers := longReplyRecvRegs rf st tid len, badge := badge }) c tid scId
      home).objects.noResizeDue := by
    rw [arm.pop_leg_hold st c tid rid _ hNo hNe]
    exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoX
  have hXf := replyRecvReplyTransfer_of_inert none st tid c grant ct hTc (fun _ => hInert)
    (arm.pop (arm.leg st c tid rid
      { registers := longReplyRecvRegs rf st tid len, badge := badge }) c tid scId home)
  obtain ⟨sTcb2, hE2, hS2, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_take arm none st epId
    tid c rid { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core ct rp ep s sTcb capAddr mi hAd hSz hT hRO hRp hE hH hS hSC hGt hR hF hXf
    (transferFrame.refl _) hNoP
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 =
          .send capAddr mi := by rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  unfold endpointReplyRecvOnCore
  rw [hEq]
  dsimp only
  rw [CapTransferSummary.capInfo_empty, replyRecvAnswerCaller_none]
  rw [arm.pop_leg_hold st c tid rid _ hNo hNe,
    receiveReturnSchedContext_msg c id _ id true _ tid hNoX hNe.symm] at hE2 hS2 hG2 ⊢
  have hAY := (ipcBufferReadsAgree_receiveReturnSchedContext true _ tid hNoX).words.trans
    ((arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid
      (arm.legReady_noResizeDue st c tid rid hNo)).trans
      (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)).words
  rw [arm.takeFrame_stagedLong st _ c tid s epId ep sTcb2 core rf len badge 0 capAddr mi
    (receiveReturnSchedContext_noResizeDue true _ tid hNoX) hAY hNe hSC (by omega) hE2 hH hS2 hG2 hR2 hF2,
    hK.queueNext, hK.regs, hK.ipcBadgeView]
  unfold performReplyRecvArmTakeDeliveredLong performReplyRecvArmTakeLegsLong
  rw [receiveReturnSchedContextFast_eq]

/-- **The reply-receive meeting a waiting sender, over every arm, its reply
leg transferring, delivered**: the arm's reply leg and pop, the transfer in
place on no endpoint, the server's context return, the take, the arm's
deschedule, the server's priority walk, then the caller's frame with the
transfer's report.  The replier and the caller enter as the words the transfer
reads of them, all read before the reply's writes. -/
@[noinline] def performReplyRecvArmTakeCapsLegsLong (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := arm.pop (arm.legReady st c tid rid) c tid scId home
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    arm.takeLegsLong (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (receiveReturnSchedContextFast true
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X) tid.val)
      c tid s epId nextCode core rf len badge

/-- The installing take over the arm, its legs (`performReplyRecvArmTakeCapsLegsLong`)
and then the server's frame (`writeTakerFrame`). -/
@[inline] def performReplyRecvArmTakeCapsDeliveredLong (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (w0 w1 w2 w3 w4 w5 : UInt64)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  writeTakerFrame (performReplyRecvArmTakeCapsLegsLong arm scId home st c tid rid epId s nextCode core
    rf len badge sv sb sroot count rv rb rroot) tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive meeting a waiting sender, its reply leg transferring,
is the specification's, over every arm**: under the guard of
`replyRecvOnCore_arm_takeDeliveredLong` (its inert transfer replaced by a granting
replier whose frame asks for `count` capabilities, `hReq`), the checked arm's
result is `performReplyRecvArmTakeCapsDeliveredLong`. -/
theorem replyRecvOnCore_arm_takeCapsDeliveredLong (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (stcb : TCB) (count : Nat)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hLen : 5 ≤ len)
    (hSzL : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
          .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmTakeCapsDeliveredLong arm scId home st c tid rid epId s
        sTcb.queueNextCode core rf len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5
        stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] count ct.spaceCells[2] ct.ipcBuffer
        ct.spaceCells[0]) := by
  have hSz := hSzL
  obtain ⟨-, hNe, hNo, -, -⟩ :=
    arm.legPop (scId := scId) (home := home) st tid c rid
      { registers := longReplyRecvRegs rf st tid len, badge := badge } core ct rp hAd
      hSz hT hRO hRp
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  have hP1 := arm.pop_leg_hold (scId := scId) (home := home) st c tid rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } hNo hNe
  have hNoX := arm.legReady_noResizeDue st c tid rid hNo
  have hAP := (arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid hNoX).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid hNoX
  generalize hX : arm.pop (arm.legReady st c tid rid) c tid scId home = X at hP1 hNoP hAP
  generalize hMsg : ({ registers := longReplyRecvRegs rf st tid len, badge := badge } :
    IpcMessage) = msg at hP1
  obtain ⟨sm, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 sm hNoP hT1
  have hHT : receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
      (X.mapTcbInPlace c (holdMessage msg)) = .ok (sm, Y1.mapTcbInPlace c (holdMessage msg)) := by
    rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoP, hT1]
    rfl
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAP)
    ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoP) c.toObjId stcb ct count hHT).1
  have hXf : replyRecvReplyTransfer none st tid c true
      (arm.pop (arm.leg st c tid rid msg) c tid scId home) =
      .ok (sm, Y1.mapTcbInPlace c (holdMessage msg)) := by
    show replyTransferCaps st tid c true _ = _
    unfold replyTransferCaps
    rw [hReq, hTgt, hP1, hHT]
  rw [← hP1] at hFr
  subst hMsg
  obtain ⟨sTcb2, hE2, hS2, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_take arm none st epId
    tid c rid { registers := longReplyRecvRegs rf st tid len, badge := badge } true core ct rp ep s sTcb capAddr mi hAd hSz hT hRO hRp hE hH hS hSC hGt hR hF hXf
    hFr ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoY)
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 =
          .send capAddr mi := by rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  unfold endpointReplyRecvOnCore
  rw [hEq]
  dsimp only
  rw [CapTransferSummary.capInfo_empty, replyRecvAnswerCaller_none]
  rw [receiveReturnSchedContext_msg c id _ id true Y1 tid hNoY hNe.symm] at hE2 hS2 hG2 ⊢
  have hAY := (ipcBufferReadsAgree_receiveReturnSchedContext true Y1 tid hNoY).words.trans
    ((ipcWordReadsAgree_receiveTransferCaps _ _ _ hNoP hT1).trans hAP.words)
  rw [arm.takeFrame_stagedLong st _ c tid s epId ep sTcb2 core rf len badge sm.capInfo capAddr mi
    (receiveReturnSchedContext_noResizeDue true Y1 tid hNoY) hAY hNe hSC (by omega) hE2 hH hS2 hG2 hR2 hF2,
    hK.queueNext, hK.regs, hK.ipcBadgeView, ← receiveReturnSchedContextFast_eq]
  have hKl := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => arm.takeLegsLong i (receiveReturnSchedContextFast true Y tid.val) c tid s epId
      sTcb.queueNextCode core rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hKl
  rw [hAP.frameCapRequestOf, hAP.capTargetOf, hT1] at hKl
  unfold performReplyRecvArmTakeCapsDeliveredLong performReplyRecvArmTakeCapsLegsLong
  rw [hX]
  dsimp only
  rw [hKl]

/-! ### The fault answer -/

/-- **The fault take's writes before the server's own frame, over the arm**:
the sender popped, made ready and woken, the server made ready, the arm's
deschedule, the server's priority walk, then the fault answer to the caller
(`performFaultAnswer`). -/
@[inline] def ReplyRecvArm.faultTakeLegs (arm : ReplyRecvArm) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (nextCode : Nat) (core : CoreId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (n off : Nat) :
    SystemState :=
  let W := (wakeThread ((storePopHead Y epId false s (ThreadId.ofOptCode nextCode)).updateTcb s
    receiverReady) s core).1
  let Z := (PriorityInheritance.propagatePipChainCrossCore (arm.desched (W.updateTcb tid
    receiverReady) tid) tid core).1
  performFaultAnswer Z c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n off

/-- **The fault take's tail, over the arm**, stages the server's message as its
frame, the arm's deschedule committed past the write
(`ReplyRecvArm.desched_hold`). -/
theorem ReplyRecvArm.faultTakeFrame_staged (arm : ReplyRecvArm) (Q : SystemState) (c tid s : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (sTcb : TCB) (core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (n off : Nat) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hNo : Q.objects.noResizeDue) (hNe : tid ≠ c)
    (hE : Q.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : Q.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace Q epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
        .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    Architecture.stageDeliveredMessage (performFaultAnswer
        (PriorityInheritance.propagatePipChainCrossCore (arm.desched
          ((wakeThread ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady) s
            core).1.updateTcb tid (callReceiverTcb (blockedSenderMessage
              (storePopHead Q epId false s sTcb.queueNext) s sTcb))) tid) tid core).1
        c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n off) tid 0 =
      writeTakerFrame
        (arm.faultTakeLegs Q c tid s epId sTcb.queueNextCode core kind label
          ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n off) tid
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5 := by
  have hG' := hG
  simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, _⟩, hRS⟩, hRN⟩, _⟩, _⟩, hRT⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hFH⟩, _⟩ := hSG'
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : epId ≠ tid.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ tid.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ tid.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨_, hFr⟩ := popHead_inPlace Q epId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace
    ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady)
    (determineTargetCore ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady) s)
    s _ hT2s rfl (by rw [updateTcb_findsInPlace _ hFr.head_tcb hFH1]; exact hFH1)
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1 hNeSR).trans hO1r
  obtain ⟨rt3, hO3r, _⟩ := hA3.get_tcb hO2r
  have hW3r : (wakeThread ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady)
      s core).1.getTcb? tid = some rt3 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  have hMsg := (blockedSender_of_routedSend (storePopHead Q epId false s sTcb.queueNext) s sTcb
    capAddr mi hR hF).2
  generalize blockedSenderMessage (storePopHead Q epId false s sTcb.queueNext) s sTcb = msgS
    at hMsg
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have hNoPY := storePopHead_noResizeDue Q epId false s sTcb.queueNext hNo
  have hNoU := updateTcb_noResizeDue _ s receiverReady hNoPY
  have hNoWY := wakeThread_noResizeDue _ s core hNoU
  have hNoWr := updateTcb_noResizeDue _ tid receiverReady hNoWY
  unfold writeTakerFrame ReplyRecvArm.faultTakeLegs
  dsimp only
  rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode]
  generalize (wakeThread ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady) s
    core).1 = W at hW3r hNoWY hNoWr ⊢
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, ← holdMessage_receiverReady,
    ← SystemState.mapTcbInPlace_mapTcbInPlace, ← SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY,
    arm.desched_hold, propagatePipChainCrossCore_msg _ _ _ _ _ _ _
      (arm.desched_noResizeDue _ tid hNoWr)]
  have hWr : (W.updateTcb tid receiverReady).getTcb? tid = some (receiverReady rt3) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, SystemState.mapTcbInPlace_getTcb?_self,
      hW3r]; rfl
  have hNoDs := arm.desched_noResizeDue _ tid hNoWr
  obtain ⟨xd, hX1, hX1s⟩ := arm.desched_ipcStateCarried _ tid tid _ hWr
  obtain ⟨x, hX, hX2s⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core hNoDs tid _ hX1
  have hXs := hX2s.trans hX1s
  have hNoZ := propagatePipChainCrossCore_noResizeDue _ tid core hNoDs
  generalize (PriorityInheritance.propagatePipChainCrossCore (arm.desched (W.updateTcb tid
    receiverReady) tid) tid core).1 = Z at hX hNoZ ⊢
  rw [performFaultAnswer_msg Z c tid _ _ _ kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf
    n off (fun e => hNe e.symm) hNoZ]
  obtain ⟨x', hX', hXs'⟩ := performFaultAnswer_ipcStateAt Z c tid kind label ip sp lr
    x0 x1 x2 x3 x4 x5 x6 x7 layout rf n off hCT hNoZ x hX
  have hNoD := performFaultAnswer_noResizeDue Z c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7
    layout rf n off hNoZ
  generalize performFaultAnswer Z c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n
    off = D at hX' hNoD ⊢
  have hSzS : msgS.registers.size ≤ 4 := by
    rw [hMsg]
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [stageDeliveredMessage_holdMessage _ _ _ hNoD hSzS, hMsg,
    Architecture.returnFrameOfMessage_regMessageBody]
  unfold writeDeliveredFrameIfReady
  rw [hX']
  dsimp only
  rw [if_pos (by rw [hXs', hXs]; rfl)]

/-- **The reply-receive answering a fault and taking a waiting sender, over
every arm, in place**: the arm's reply leg with no message
(`ReplyRecvArm.faultLeg`) and pop, the server's context return, the take, the
arm's deschedule, the server's priority walk and the fault answer
(`ReplyRecvArm.faultTakeLegs`). -/
@[noinline] def performReplyRecvArmFaultTakeLegs (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) : SystemState :=
  arm.faultTakeLegs (receiveReturnSchedContextFast true
    (arm.pop (arm.faultLeg st c tid rid) c tid scId home) tid.val) c tid s epId nextCode core
    kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf (Architecture.regMessageLength layout len) 0

/-- The fault take over the arm, its legs and then the server's frame, each out
of line so the arm releases the server's register file between them. -/
@[inline] def performReplyRecvArmFaultTakeDelivered (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  writeTakerFrame (performReplyRecvArmFaultTakeLegs arm scId home st c tid rid epId s nextCode core
    kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf len) tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive answering a fault and taking a waiting sender is the
specification's, over every arm**: under the arm's reply-leg guard, for a
caller carrying fault `tf` and a sender `s` at the head of the send queue
blocked by a routed capability-free send, not delivering a fault, whose take
writes only its slots (every check read on the pre-state), the arm's
transition, then the server's staged message, is
`performReplyRecvArmFaultTakeDelivered`. -/
theorem replyRecvTransferOnCore_arm_faultTake (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (grant : Bool) (core : CoreId)
    (ct : TCB) (rp : Reply) (ep : Endpoint) (tf : ThreadFault)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
          .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match replyRecvTransferOnCore epId tid rid c label
        { registers := Architecture.regMessageBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmFaultTakeDelivered arm scId home st c tid rid epId s
        sTcb.queueNextCode core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf len
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨-, hNe, hNo, -, -⟩ := arm.legPop (scId := scId) (home := home) st tid c rid
    IpcMessage.empty core ct rp hAd (by simp [IpcMessage.empty]) hT hRO hRp
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label
    { registers := Architecture.regMessageBody layout rf len, badge := badge } hTc hPF
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid
    (arm.leg_noResizeDue st c tid rid IpcMessage.empty hNo)
  have hXf : replyRecvReplyTransfer (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regMessageBody layout rf len, badge := badge }) st tid c grant
      (arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home) =
      .ok ({ results := #[] }, arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home) := by
    rw [hAns]; rfl
  obtain ⟨sTcb2, hE2, hS2, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_take arm _ st epId tid c
    rid IpcMessage.empty grant core ct rp ep s sTcb capAddr mi hAd (by simp [IpcMessage.empty]) hT
    hRO hRp hE hH hS hSC hGt hR hF hXf (transferFrame.refl _) hNoP
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 =
          .send capAddr mi := by rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regMessageBody layout rf len, badge := badge })
      { registers := Architecture.regMessageBody layout rf len, badge := badge } =
      IpcMessage.empty := by rw [hAns]; rfl
  unfold replyRecvTransferOnCore
  rw [hL, hEq]
  dsimp only
  rw [CapTransferSummary.capInfo_empty, hAns]
  unfold replyRecvAnswerCaller
  dsimp only
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF _ _ layout rf
    (Architecture.regMessageLength layout len) 0
    (by simp only [Architecture.regMessageBody_size, Nat.min_self])
    (fun i hi => wordAt_regMessageBody layout rf len i hi)]
  rw [arm.faultTakeFrame_staged _ c tid s epId ep sTcb2 core _ label _ _ _ _ _ _ _ _ _ _ _
    layout rf _ 0 capAddr mi (receiveReturnSchedContext_noResizeDue true _ tid hNoP) hNe hE2 hH
    hS2 hG2 hR2 hF2, hK.queueNext, hK.regs, hK.ipcBadgeView]
  unfold performReplyRecvArmFaultTakeDelivered performReplyRecvArmFaultTakeLegs
  rw [receiveReturnSchedContextFast_eq, arm.faultLeg_eq]

/-! ### The long fault answer -/

/-- A long fault reply's word reads only buffer words, so two states reading
every buffer alike read it alike. -/
theorem faultReplyWordLong_congr {X X' : SystemState} (h : ipcWordReadsAgree X' X)
    (s : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (len i : Nat) (fb : UInt64) :
    faultReplyWordLong X' s rf len i fb = faultReplyWordLong X s rf len i fb := by
  unfold faultReplyWordLong
  rw [h.overflowWordAt]

theorem performFaultAnswerLong_noResizeDue (X : SystemState) (c : SeLe4n.ThreadId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (hNo : X.objects.noResizeDue) :
    (performFaultAnswerLong X c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 s rf
      len).objects.noResizeDue := by
  unfold performFaultAnswerLong applyFaultRestart faultAbandonOnCore
  split
  · exact updateTcb_noResizeDue _ _ _ hNo
  · split
    · exact updateTcb_noResizeDue _ _ _ (removeRunnableOnCore_noResizeDue _ _ _ hNo)
    · split
      · exact updateTcb_noResizeDue _ _ _ hNo
      · exact updateTcb_noResizeDue _ _ _ hNo

/-- **The long fault answer commutes past another thread's message-slot
write**: the write keeps every buffer word the answer reads, and moves nothing
else it reads or writes. -/
theorem performFaultAnswerLong_msg (X : SystemState) (c r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (hNe : c ≠ r) (hNo : X.objects.noResizeDue) :
    performFaultAnswerLong (X.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c kind label ip sp lr
        x0 x1 x2 x3 x4 x5 x6 x7 s rf len =
      (performFaultAnswerLong X c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 s rf
        len).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  have hW : ∀ i fb, faultReplyWordLong (X.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) s rf len
      i fb = faultReplyWordLong X s rf len i fb := fun i fb =>
    faultReplyWordLong_congr (ipcBufferReadsAgree_mapTcbInPlace X r (TCB.withMessageSlots ρ μ π)
      (fun _ => ⟨rfl, rfl⟩)).words
      s rf len i fb
  unfold performFaultAnswerLong
  simp only [hW]
  unfold applyFaultRestart faultAbandonOnCore faultAbandonCore
  rw [placedCoreOf?_msg, determineTargetCore_msg]
  split
  · exact updateTcb_msg r ρ μ π X c _ hNo (fun h => absurd h hNe)
  · split
    · rw [removeRunnableOnCore_msg]
      exact updateTcb_msg r ρ μ π _ c _ (removeRunnableOnCore_noResizeDue _ _ _ hNo)
        (fun h => absurd h hNe)
    · split
      · exact updateTcb_msg r ρ μ π X c _ hNo (fun h => absurd h hNe)
      · exact updateTcb_msg r ρ μ π X c _ hNo (fun h => absurd h hNe)

/-- **The long fault take's writes before the server's own frame, over the
arm**: as `ReplyRecvArm.faultTakeLegs`, the answer's words past MR3 read from
the replier's buffer (`performFaultAnswerLong`). -/
@[inline] def ReplyRecvArm.faultTakeLegsLong (arm : ReplyRecvArm) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (nextCode : Nat) (core : CoreId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (rf : SeLe4n.RegisterFile) (len : Nat) : SystemState :=
  let W := (wakeThread ((storePopHead Y epId false s (ThreadId.ofOptCode nextCode)).updateTcb s
    receiverReady) s core).1
  let Z := (PriorityInheritance.propagatePipChainCrossCore (arm.desched (W.updateTcb tid
    receiverReady) tid) tid core).1
  performFaultAnswerLong Z c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 tid rf len

/-- **The long fault take's tail, over the arm**, stages the server's message
as its frame. -/
theorem ReplyRecvArm.faultTakeFrame_stagedLong (arm : ReplyRecvArm) (Q : SystemState) (c tid s : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (sTcb : TCB) (core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (rf : SeLe4n.RegisterFile) (len : Nat) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hNo : Q.objects.noResizeDue) (hNe : tid ≠ c)
    (hE : Q.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : Q.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace Q epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
        .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    Architecture.stageDeliveredMessage (performFaultAnswerLong
        (PriorityInheritance.propagatePipChainCrossCore (arm.desched
          ((wakeThread ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady) s
            core).1.updateTcb tid (callReceiverTcb (blockedSenderMessage
              (storePopHead Q epId false s sTcb.queueNext) s sTcb))) tid) tid core).1
        c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 tid rf len) tid 0 =
      writeTakerFrame
        (arm.faultTakeLegsLong Q c tid s epId sTcb.queueNextCode core kind label
          ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 rf len) tid
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5 := by
  have hG' := hG
  simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, _⟩, hRS⟩, hRN⟩, _⟩, _⟩, hRT⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hFH⟩, _⟩ := hSG'
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : epId ≠ tid.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ tid.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ tid.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨_, hFr⟩ := popHead_inPlace Q epId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace
    ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady)
    (determineTargetCore ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady) s)
    s _ hT2s rfl (by rw [updateTcb_findsInPlace _ hFr.head_tcb hFH1]; exact hFH1)
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1 hNeSR).trans hO1r
  obtain ⟨rt3, hO3r, _⟩ := hA3.get_tcb hO2r
  have hW3r : (wakeThread ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady)
      s core).1.getTcb? tid = some rt3 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  have hMsg := (blockedSender_of_routedSend (storePopHead Q epId false s sTcb.queueNext) s sTcb
    capAddr mi hR hF).2
  generalize blockedSenderMessage (storePopHead Q epId false s sTcb.queueNext) s sTcb = msgS
    at hMsg
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have hNoPY := storePopHead_noResizeDue Q epId false s sTcb.queueNext hNo
  have hNoU := updateTcb_noResizeDue _ s receiverReady hNoPY
  have hNoWY := wakeThread_noResizeDue _ s core hNoU
  have hNoWr := updateTcb_noResizeDue _ tid receiverReady hNoWY
  unfold writeTakerFrame ReplyRecvArm.faultTakeLegsLong
  dsimp only
  rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode]
  generalize (wakeThread ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady) s
    core).1 = W at hW3r hNoWY hNoWr ⊢
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, ← holdMessage_receiverReady,
    ← SystemState.mapTcbInPlace_mapTcbInPlace, ← SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY,
    arm.desched_hold, propagatePipChainCrossCore_msg _ _ _ _ _ _ _
      (arm.desched_noResizeDue _ tid hNoWr)]
  have hWr : (W.updateTcb tid receiverReady).getTcb? tid = some (receiverReady rt3) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, SystemState.mapTcbInPlace_getTcb?_self,
      hW3r]; rfl
  have hNoDs := arm.desched_noResizeDue _ tid hNoWr
  obtain ⟨xd, hX1, hX1s⟩ := arm.desched_ipcStateCarried _ tid tid _ hWr
  obtain ⟨x, hX, hX2s⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core hNoDs tid _ hX1
  have hXs := hX2s.trans hX1s
  have hNoZ := propagatePipChainCrossCore_noResizeDue _ tid core hNoDs
  generalize (PriorityInheritance.propagatePipChainCrossCore (arm.desched (W.updateTcb tid
    receiverReady) tid) tid core).1 = Z at hX hNoZ ⊢
  rw [performFaultAnswerLong_msg Z c tid _ _ _ kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 tid rf
    len (fun e => hNe e.symm) hNoZ]
  obtain ⟨x', hX', hXs'⟩ := performFaultAnswerLong_ipcStateAt Z c tid kind label ip sp lr
    x0 x1 x2 x3 x4 x5 x6 x7 tid rf len hCT hNoZ x hX
  have hNoD := performFaultAnswerLong_noResizeDue Z c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7
    tid rf len hNoZ
  generalize performFaultAnswerLong Z c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 tid rf
    len = D at hX' hNoD ⊢
  have hSzS : msgS.registers.size ≤ 4 := by
    rw [hMsg]
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [stageDeliveredMessage_holdMessage _ _ _ hNoD hSzS, hMsg,
    Architecture.returnFrameOfMessage_regMessageBody]
  unfold writeDeliveredFrameIfReady
  rw [hX']
  dsimp only
  rw [if_pos (by rw [hXs', hXs]; rfl)]

/-- **The take's writes keep every buffer read**: the pop, the sender's and
the server's state writes, the wake, the arm's deschedule and the priority
walk write no buffer. -/
theorem ReplyRecvArm.takeState_wordsAgree (arm : ReplyRecvArm) (Q : SystemState)
    (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (tid : SeLe4n.ThreadId) (core : CoreId) (m : IpcMessage) (hNo : Q.objects.noResizeDue) :
    ipcWordReadsAgree (PriorityInheritance.propagatePipChainCrossCore (arm.desched
      ((wakeThread ((storePopHead Q epId false s next).updateTcb s receiverReady) s
        core).1.updateTcb tid (callReceiverTcb m)) tid) tid core).1 Q := by
  have hNoPY := storePopHead_noResizeDue Q epId false s next hNo
  have hNoU := updateTcb_noResizeDue _ s receiverReady hNoPY
  have hNoWY := wakeThread_noResizeDue _ s core hNoU
  have hNoWm := updateTcb_noResizeDue _ tid (callReceiverTcb m) hNoWY
  exact ((ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core
    (arm.desched_noResizeDue _ tid hNoWm)).trans ((arm.ipcBufferReadsAgree_desched _ tid).trans
    ((ipcBufferReadsAgree_updateTcb _ tid (callReceiverTcb m) (fun _ => ⟨rfl, rfl⟩) hNoWY).trans
    ((ipcBufferReadsAgree_wakeThread _ s core hNoU).trans
    ((ipcBufferReadsAgree_updateTcb _ s receiverReady (fun _ => ⟨rfl, rfl⟩) hNoPY).trans
    (ipcBufferReadsAgree_storePopHead Q epId false s next hNo)))))).words

/-- **The long reply-receive answering a fault and taking a waiting sender,
over every arm, in place**: as `performReplyRecvArmFaultTakeLegs`, the
answer's words past MR3 read from the replier's buffer. -/
@[noinline] def performReplyRecvArmFaultTakeLegsLong (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (rf : SeLe4n.RegisterFile) (len : Nat) :
    SystemState :=
  arm.faultTakeLegsLong (receiveReturnSchedContextFast true
    (arm.pop (arm.faultLeg st c tid rid) c tid scId home) tid.val) c tid s epId nextCode core
    kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 rf len

/-- The long fault take over the arm, its legs and then the server's frame. -/
@[inline] def performReplyRecvArmFaultTakeDeliveredLong (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (rf : SeLe4n.RegisterFile) (len : Nat)
    (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  writeTakerFrame (performReplyRecvArmFaultTakeLegsLong arm scId home st c tid rid epId s nextCode
    core kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 rf len) tid w0 w1 w2 w3 w4 w5

/-- **The long reply-receive answering a fault and taking a waiting sender is
the specification's, over every arm**: as `replyRecvTransferOnCore_arm_faultTake`,
the reply of more than four words. -/
theorem replyRecvTransferOnCore_arm_faultTakeLong (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (tf : ThreadFault)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct) (hLen : 4 ≤ len)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
          .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match replyRecvTransferOnCore epId tid rid c label
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmFaultTakeDeliveredLong arm scId home st c tid rid epId s
        sTcb.queueNextCode core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨-, hNe, hNo, -, -⟩ := arm.legPop (scId := scId) (home := home) st tid c rid
    IpcMessage.empty core ct rp hAd (by simp [IpcMessage.empty]) hT hRO hRp
  let msg : IpcMessage := { registers := longReplyRecvRegs rf st tid len, badge := badge }
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label msg hTc hPF
  have hNoL := arm.leg_noResizeDue st c tid rid IpcMessage.empty hNo
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid hNoL
  have hXf : replyRecvReplyTransfer (replyRecvCallerFaultAnswer? st c label msg) st tid c grant
      (arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home) =
      .ok ({ results := #[] }, arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home) := by
    rw [hAns]; rfl
  obtain ⟨sTcb2, hE2, hS2, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_take arm _ st epId tid c
    rid IpcMessage.empty grant core ct rp ep s sTcb capAddr mi hAd (by simp [IpcMessage.empty]) hT
    hRO hRp hE hH hS hSC hGt hR hF hXf (transferFrame.refl _) hNoP
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 =
          .send capAddr mi := by rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label msg) msg =
      IpcMessage.empty := by rw [hAns]; rfl
  have hNoQ := receiveReturnSchedContext_noResizeDue true _ tid hNoP
  have hW := (arm.takeState_wordsAgree _ epId s sTcb2.queueNext tid core
    (blockedSenderMessage (storePopHead (receiveReturnSchedContext true
      (arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home) tid) epId false s
      sTcb2.queueNext) s sTcb2) hNoQ).trans
    ((ipcBufferReadsAgree_receiveReturnSchedContext true _ tid hNoP).trans
      ((arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid hNoL).trans
        (arm.ipcBufferReadsAgree_leg st c tid rid IpcMessage.empty hNo))).words
  unfold replyRecvTransferOnCore
  rw [hL, hEq]
  dsimp only
  rw [CapTransferSummary.capInfo_empty]
  unfold replyRecvAnswerCaller
  rw [hAns]
  dsimp only
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ tid rf len
    (replyWordOr_longReplyRecvRegs st _ tid rf len label hLen hW)]
  rw [arm.faultTakeFrame_stagedLong _ c tid s epId ep sTcb2 core _ label _ _ _ _ _ _ _ _ _ _ _
    rf len capAddr mi hNoQ hNe hE2 hH hS2 hG2 hR2 hF2, hK.queueNext, hK.regs, hK.ipcBadgeView]
  unfold performReplyRecvArmFaultTakeDeliveredLong performReplyRecvArmFaultTakeLegsLong
  rw [receiveReturnSchedContextFast_eq, arm.faultLeg_eq]

/-! ### The arm's guard, read on the pre-state -/

/-- Whether caller `ct` is blocked on a reply from the server `tid`. -/
@[inline] def replyRecvCallerAwaits (ct : TCB) (tid : SeLe4n.ThreadId) : Bool :=
  match ct.ipcState with
  | .blockedOnReply _ (some server) => server.val == tid.val
  | _ => false

/-- Whether caller `ct` is blocked on a reply recording no server. -/
@[inline] def replyRecvCallerAwaitsNone (ct : TCB) : Bool :=
  match ct.ipcState with
  | .blockedOnReply _ none => true
  | _ => false

theorem replyRecvCallerAwaits_spec {ct : TCB} {tid : SeLe4n.ThreadId}
    (h : replyRecvCallerAwaits ct tid = true) : ∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid) := by
  unfold replyRecvCallerAwaits at h
  split at h
  · next ep0 server hS =>
    have : server = tid := by
      cases server; cases tid; simp only [beq_iff_eq] at h; subst h; rfl
    subst this
    exact ⟨ep0, hS⟩
  · cases h

theorem replyRecvCallerAwaitsNone_spec {ct : TCB} (h : replyRecvCallerAwaitsNone ct = true) :
    ∃ ep0, ct.ipcState = .blockedOnReply ep0 none := by
  unfold replyRecvCallerAwaitsNone at h
  split at h
  · next ep0 hS => exact ⟨ep0, hS⟩
  · cases h

/-- **The arm's reply-leg guard as a test on the pre-state**, the caller `ct`:
`ReplyRecvArm.LegAdmits` at the context the reply heads and the caller's home
(`ReplyRecvArm.legGuard_spec`). -/
@[noinline] def ReplyRecvArm.legGuard : ReplyRecvArm → SystemState → SeLe4n.ThreadId →
    SeLe4n.ThreadId → SeLe4n.ReplyId → TCB → Bool
  | .rendezvous, st, tid, c, rid, ct =>
      replyRecvCallerAwaits ct tid && replyWakesInPlace st c ct rid && tid.val != c.val
  | .donated, st, tid, c, rid, ct =>
      replyRecvCallerAwaits ct tid && !tid.isReserved &&
        replyPopsInPlace st c ct.scBindingScCode tid rid
  | .held, st, tid, c, rid, ct =>
      replyRecvCallerAwaits ct tid && replyHeldPopsInPlace st c ct.scBindingScCode tid rid
  | .unheld, st, tid, c, rid, ct =>
      replyRecvCallerAwaitsNone ct && replyUnheldPopsInPlace st c rid && tid.val != c.val
  | .unlinked, st, tid, c, rid, ct =>
      replyRecvCallerAwaitsNone ct && replyUnlinkedInPlace st c rid && tid.val != c.val

theorem ReplyRecvArm.legGuard_spec {arm : ReplyRecvArm} {st : SystemState}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {ct : TCB}
    (h : arm.legGuard st tid c rid ct = true) :
    arm.LegAdmits ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st tid c rid ct := by
  have ne : (tid.val != c.val) = true → tid ≠ c := by
    intro h e; subst e; simp at h
  cases arm <;> simp only [ReplyRecvArm.legGuard, Bool.and_eq_true, Bool.not_eq_true'] at h
  · exact ⟨replyRecvCallerAwaits_spec h.1.1, h.1.2, ne h.2⟩
  · exact ⟨replyRecvCallerAwaits_spec h.1.1, h.1.2, h.2, rfl, rfl⟩
  · exact ⟨replyRecvCallerAwaits_spec h.1, h.2, rfl⟩
  · exact ⟨replyRecvCallerAwaitsNone_spec h.1.1, h.1.2, ne h.2, rfl, rfl⟩
  · exact ⟨replyRecvCallerAwaitsNone_spec h.1.1, h.1.2, ne h.2⟩

/-- **Whether the endpoint's send queue offers a sender the receive leg takes
in place**: its head is not the caller, delivers no fault, and its take writes
only its slots (`receiveTakesInPlace`), each read on the pre-state. -/
@[inline] def replyRecvSenderTakes (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) : Bool :=
  match st.getEndpoint? epId with
  | some ep =>
      match ep.sendQ.head with
      | some s =>
          s.val != c.val &&
          (match st.getTcb? s with
           | some sTcb => !sTcb.ipcFaultSend && receiveTakesInPlace st epId tid s sTcb
           | none => false)
      | none => false
  | none => false

theorem replyRecvSenderTakes_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} (h : replyRecvSenderTakes st epId tid c = true) :
    ∃ (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB),
      st.getEndpoint? epId = some ep ∧ ep.sendQ.head = some s ∧ st.getTcb? s = some sTcb ∧
      s ≠ c ∧ sTcb.ipcFaultSend = false ∧ receiveTakesInPlace st epId tid s sTcb = true := by
  unfold replyRecvSenderTakes at h
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at h; cases h
  | some ep =>
  rw [hEp] at h
  dsimp only at h
  cases hH : ep.sendQ.head with
  | none => rw [hH] at h; cases h
  | some s =>
  rw [hH] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hSC, hT⟩ := h
  have hSC' : s ≠ c := fun e => by subst e; simp at hSC
  cases hTs : st.getTcb? s with
  | none => rw [hTs] at hT; cases hT
  | some sTcb =>
  rw [hTs] at hT
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hT
  exact ⟨ep, s, sTcb, rfl, hH, hTs, hSC', hT.1, hT.2⟩

end SeLe4n.Kernel
