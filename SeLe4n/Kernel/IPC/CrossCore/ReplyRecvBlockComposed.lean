/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvDonatedInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyHeldInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvUnheldInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyCapsReturnDelivered
import SeLe4n.Kernel.IPC.CrossCore.LongReplyRecvPopInPlace
import SeLe4n.Kernel.IPC.CrossCore.LongFaultAnswerInPlace

/-!
# The blocking reply-receive, composed over its reply arm

WS-SX SX25.  A reply-receive whose receive leg blocks runs one reply leg, one
pop and one block, whatever the reply's arm: the reply's writes
(`storeReplyRendezvous` when the caller recorded the server,
`storeReplyLeg` when it recorded none), the arm's pop (none, the donated pop
and its settle, the held pop, the unheld pop and its settle, or none on a reply
linked to nothing), the server's context return on its bound notification, its
block on the endpoint, its removal from its core (and, on the donated arm, its
deschedule from the context it gave back), then its priority walk.  The arm is
data (`ReplyRecvArm`), so the shapes the receive answers (the short and the
long message, the capability transfer, the fault) are each written once over
it, and joined to the specification through one equality per arm
(`replyRecvAnsweringOnCore_arm_inPlace`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- **The reply arm of a reply-receive**: what the reply leg pops, read on the
pre-state.  The donated and unheld arms carry the context they return and the
caller's home core, the held arm the context the server keeps. -/
inductive ReplyRecvArm where
  /-- The caller recorded the server and lent it nothing. -/
  | rendezvous
  /-- The caller lent the server its context; the pop returns it. -/
  | donated (scId : SeLe4n.SchedContextId) (home : CoreId)
  /-- The server keeps the context the reply object heads. -/
  | held (scId : SeLe4n.SchedContextId)
  /-- The caller recorded no server; the context no thread holds returns to it. -/
  | unheld (scId : SeLe4n.SchedContextId) (home : CoreId)
  /-- The caller recorded no server; its reply object links to nothing. -/
  | unlinked

namespace ReplyRecvArm

/-- Whether the arm's caller recorded the server (the reply leg's rendezvous). -/
@[inline] def recordsServer : ReplyRecvArm → Bool
  | .rendezvous => true
  | .donated .. => true
  | .held _ => true
  | .unheld .. => false
  | .unlinked => false

/-- The reply leg's writes, the caller woken holding no message yet. -/
@[inline] def legReady (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : SystemState :=
  if arm.recordsServer then storeReplyRendezvousReady st c tid rid else storeReplyLegReady st c rid

/-- The reply leg as the specification runs it, the caller holding `msg`. -/
@[inline] def leg (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) : SystemState :=
  if arm.recordsServer then storeReplyRendezvous st c tid rid msg else storeReplyLeg st c rid msg

/-- The arm's pop, after the reply leg. -/
@[inline] def pop : ReplyRecvArm → SystemState → SeLe4n.ThreadId → SeLe4n.ThreadId → SystemState
  | .rendezvous, X, _, _ => X
  | .donated scId home, X, c, tid => popDonationSettledInPlace X c tid scId home
  | .held scId, X, _, tid => keepDonatedSchedContextInPlace X tid scId
  | .unheld scId home, X, c, _ =>
      SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace X c scId) home scId
  | .unlinked, X, _, _ => X

/-- The server's deschedule after its block: only the donated arm's server gave
back the context it ran on. -/
@[inline] def desched : ReplyRecvArm → SystemState → SeLe4n.ThreadId → SystemState
  | .donated .., X, tid => descheduleAtPlacement X tid
  | _, X, _ => X

/-- The server's receive block on the state the pop leaves: its context return
on its bound notification, its block on the endpoint, its removal from its
core. -/
@[inline] def blocked (Y : SystemState) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) : SystemState :=
  removeRunnableOnCore (storeReceiveBlock (receiveReturnSchedContext true Y tid) epId tid tailCode
    (SeLe4n.ReplyId.optCode (some rid))) tid core

/-- The receive leg's tail: the block, the arm's deschedule, the priority walk. -/
@[inline] def tail (arm : ReplyRecvArm) (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) : SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore (arm.desched (blocked Y tid rid epId tailCode core)
    tid) tid core).1

/-- The tail as it is compiled: the context return read off the server's code. -/
@[inline] def tailFast (arm : ReplyRecvArm) (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) : SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore (arm.desched (removeRunnableOnCore
    (storeReceiveBlock (receiveReturnSchedContextFast true Y tid.val) epId tid tailCode
      (rid.val + 1)) tid core) tid) tid core).1

theorem tailFast_eq (arm : ReplyRecvArm) (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) :
    arm.tailFast Y tid rid epId tailCode core = arm.tail Y tid rid epId tailCode core := by
  unfold tailFast tail blocked
  rw [receiveReturnSchedContextFast_eq]
  rfl

/-- **The blocking reply-receive's writes, the caller holding no message**: the
reply leg, the pop and the tail, in place. -/
@[inline] def ready (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) : SystemState :=
  arm.tailFast (arm.pop (arm.legReady st c tid rid) c tid) tid rid epId tailCode core

/-! ### What the arm's writes keep -/

theorem leg_eq_hold (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (hNo : st.objects.noResizeDue) :
    arm.leg st c tid rid msg = (arm.legReady st c tid rid).mapTcbInPlace c (holdMessage msg) := by
  unfold leg legReady
  split
  · exact storeReplyRendezvous_eq_hold _ _ _ _ _ hNo
  · exact storeReplyLeg_eq_hold _ _ _ _ hNo

theorem legReady_noResizeDue (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    (arm.legReady st c tid rid).objects.noResizeDue := by
  unfold legReady
  split
  · exact storeReplyRendezvousReady_noResizeDue _ _ _ _ hNo
  · exact storeReplyLegReady_noResizeDue _ _ _ hNo

theorem leg_noResizeDue (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (hNo : st.objects.noResizeDue) :
    (arm.leg st c tid rid msg).objects.noResizeDue := by
  rw [leg_eq_hold _ _ _ _ _ _ hNo, SystemState.mapTcbInPlace_noResizeDue]
  exact legReady_noResizeDue _ _ _ _ _ hNo

theorem ipcBufferReadsAgree_legReady (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (arm.legReady st c tid rid) st := by
  unfold legReady
  split
  · exact ipcBufferReadsAgree_storeReplyRendezvousReady _ _ _ _ hNo
  · exact ipcBufferReadsAgree_storeReplyLegReady _ _ _ hNo

theorem pop_noResizeDue (arm : ReplyRecvArm) (X : SystemState) (c tid : SeLe4n.ThreadId)
    (hNo : X.objects.noResizeDue) : (arm.pop X c tid).objects.noResizeDue := by
  cases arm with
  | rendezvous => exact hNo
  | donated scId home => exact popDonationSettledInPlace_noResizeDue _ _ _ _ _ hNo
  | held scId => exact keepDonatedSchedContextInPlace_noResizeDue _ _ _ hNo
  | unheld scId home =>
    exact settleReturnedContext_noResizeDue _ _ _
      (returnUnheldSchedContextInPlace_noResizeDue _ _ _ hNo)
  | unlinked => exact hNo

/-- **The pop commutes with a message write to any thread but the server**. -/
theorem pop_msg (arm : ReplyRecvArm) (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (X : SystemState) (c tid : SeLe4n.ThreadId) (hNo : X.objects.noResizeDue)
    (hR : r ≠ tid) :
    arm.pop (X.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c tid =
      (arm.pop X c tid).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  cases arm with
  | rendezvous => rfl
  | donated scId home => exact popDonationSettledInPlace_msg r ρ μ π X c tid scId home hNo hR
  | held scId => exact keepDonatedSchedContextInPlace_msg r ρ μ π X tid scId hNo hR
  | unheld scId home =>
    show SchedContextOps.settleReturnedContext _ home scId = _
    rw [returnUnheldSchedContextInPlace_msg r ρ μ π X c scId hNo, settleReturnedContext_msg]
    rfl
  | unlinked => rfl

/-- **The held pop keeps every read**, as the donation pop does: it writes the
context, the reply links and the holder's binding. -/
theorem ipcBufferReadsAgree_keepDonatedSchedContextInPlace (st : SystemState)
    (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (keepDonatedSchedContextInPlace st holder scId) st := by
  unfold keepDonatedSchedContextInPlace
  split
  · exact .refl st
  split
  · exact .refl st
  rename_i hr _
  split
  · exact .refl st
  rename_i r _
  split
  · exact .refl st
  dsimp only
  refine (ipcBufferReadsAgree_updateTcb _ _ _ ?_ ?_).trans ?_
  · exact fun _ => ⟨rfl, rfl⟩
  · exact (ipcBufferReadsAgree_popLinks st scId _ hr r.prev _ _ hNo).2
  · exact (ipcBufferReadsAgree_popLinks st scId _ hr r.prev _ _ hNo).1

theorem ipcBufferReadsAgree_pop (arm : ReplyRecvArm) (X : SystemState) (c tid : SeLe4n.ThreadId)
    (hNo : X.objects.noResizeDue) : ipcBufferReadsAgree (arm.pop X c tid) X := by
  cases arm with
  | rendezvous => exact .refl X
  | donated scId home =>
    exact (ipcBufferReadsAgree_settleReturnedContext _ home scId).trans
      (ipcBufferReadsAgree_returnDonatedSchedContextInPlace X tid c scId hNo)
  | held scId => exact ipcBufferReadsAgree_keepDonatedSchedContextInPlace X tid scId hNo
  | unheld scId home =>
    exact (ipcBufferReadsAgree_settleReturnedContext _ home scId).trans
      (ipcBufferReadsAgree_returnUnheldSchedContextInPlace X c scId hNo)
  | unlinked => exact .refl X

theorem desched_noResizeDue (arm : ReplyRecvArm) (X : SystemState) (tid : SeLe4n.ThreadId)
    (hNo : X.objects.noResizeDue) : (arm.desched X tid).objects.noResizeDue := by
  cases arm <;> first | exact hNo | exact descheduleAtPlacement_noResizeDue _ _ hNo

theorem desched_msg (arm : ReplyRecvArm) (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (X : SystemState) (tid : SeLe4n.ThreadId) :
    arm.desched (X.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid =
      (arm.desched X tid).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  cases arm <;> first | rfl | exact descheduleAtPlacement_msg _ _ _ _ _ _

theorem desched_ipcStateCarried (arm : ReplyRecvArm) (X : SystemState) (tid : SeLe4n.ThreadId) :
    ipcStateCarried X (arm.desched X tid) := by
  cases arm <;> first | exact descheduleAtPlacement_ipcStateCarried _ _ |
    exact ipcStateCarried_of_objects_eq rfl

theorem ipcBufferReadsAgree_desched (arm : ReplyRecvArm) (X : SystemState)
    (tid : SeLe4n.ThreadId) : ipcBufferReadsAgree (arm.desched X tid) X := by
  cases arm <;> first | exact .refl X | exact ipcBufferReadsAgree_descheduleAtPlacement _ _

theorem blocked_noResizeDue (Y : SystemState) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) (hNo : Y.objects.noResizeDue) :
    (blocked Y tid rid epId tailCode core).objects.noResizeDue :=
  removeRunnableOnCore_noResizeDue _ _ _ (storeReceiveBlock_noResizeDue _ _ _ _ _
    (receiveReturnSchedContext_noResizeDue _ _ _ hNo))

theorem tail_noResizeDue (arm : ReplyRecvArm) (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (hNo : Y.objects.noResizeDue) : (arm.tail Y tid rid epId tailCode core).objects.noResizeDue :=
  propagatePipChainCrossCore_noResizeDue _ _ _ (desched_noResizeDue _ _ _
    (blocked_noResizeDue _ _ _ _ _ _ hNo))

/-- **The block commutes with the caller's held message.** -/
theorem blocked_msg (r : SeLe4n.ThreadId) (msg : IpcMessage) (Y : SystemState)
    (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (core : CoreId) (hNo : Y.objects.noResizeDue) (hR : r ≠ tid) :
    blocked (Y.mapTcbInPlace r (holdMessage msg)) tid rid epId tailCode core =
      (blocked Y tid rid epId tailCode core).mapTcbInPlace r (holdMessage msg) := by
  have hNoR := receiveReturnSchedContext_noResizeDue true Y tid hNo
  unfold blocked
  rw [receiveReturnSchedContext_msg r id (fun _ => some msg) id true _ tid hNo hR,
    storeReceiveBlock_msg _ _ _ _ _ _ _ hNoR (fun e => hR e.symm), removeRunnableOnCore_msg]

/-- **The tail commutes with the caller's held message.** -/
theorem tail_msg (arm : ReplyRecvArm) (r : SeLe4n.ThreadId) (msg : IpcMessage)
    (Y : SystemState) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) (hNo : Y.objects.noResizeDue)
    (hR : r ≠ tid) :
    arm.tail (Y.mapTcbInPlace r (holdMessage msg)) tid rid epId tailCode core =
      (arm.tail Y tid rid epId tailCode core).mapTcbInPlace r (holdMessage msg) := by
  have hNoR := receiveReturnSchedContext_noResizeDue true Y tid hNo
  have h3 : (removeRunnableOnCore (storeReceiveBlock (receiveReturnSchedContext true Y tid) epId tid
      tailCode (SeLe4n.ReplyId.optCode (some rid))) tid core).objects.noResizeDue :=
    blocked_noResizeDue Y tid rid epId tailCode core hNo
  unfold tail blocked
  rw [receiveReturnSchedContext_msg r id (fun _ => some msg) id true _ tid hNo hR,
    storeReceiveBlock_msg _ _ _ _ _ _ _ hNoR (fun e => hR e.symm), removeRunnableOnCore_msg,
    desched_msg, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ (desched_noResizeDue _ _ _ h3)]

theorem ipcBufferReadsAgree_tail (arm : ReplyRecvArm) (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (hNo : Y.objects.noResizeDue) :
    ipcBufferReadsAgree (arm.tail Y tid rid epId tailCode core) Y := by
  have hNoR := receiveReturnSchedContext_noResizeDue true Y tid hNo
  have h3 := blocked_noResizeDue Y tid rid epId tailCode core hNo
  exact (ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core
      (desched_noResizeDue _ _ _ h3)).trans
    ((ipcBufferReadsAgree_desched _ _ tid).trans
      ((ipcBufferReadsAgree_removeRunnableOnCore _ tid core).trans
        ((ipcBufferReadsAgree_storeReceiveBlock _ epId tid tailCode _ hNoR).trans
          (ipcBufferReadsAgree_receiveReturnSchedContext true Y tid hNo))))

/-! ### The arm's guard and its one equality to the specification -/

/-- **What the arm's in-place path asks of the pre-state**, beside the checks
every arm shares: the caller blocked on the reply naming the server or none,
the arm's pop guard, the server's admission to the block, and the popped
context and the caller's home as the specification reads them. -/
def Admits : ReplyRecvArm → SystemState → SeLe4n.ThreadId → SeLe4n.ThreadId → SeLe4n.ReplyId →
    TCB → TCB → Reply → Prop
  | .rendezvous, st, tid, c, rid, ct, rt, rp =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid)) ∧
      replyWakesInPlace st c ct rid = true ∧ tid ≠ c ∧ receiveBlockAdmits rt = true ∧
      rp.consumed.isFree = true
  | .donated scId home, st, tid, c, rid, ct, rt, _ =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid)) ∧ tid.isReserved = false ∧
      replyPopsInPlace st c ct.scBindingScCode tid rid = true ∧ enqueueAdmits rt = true ∧
      scId = ⟨replyHeadContextCode st rid - 1⟩ ∧ home = determineTargetCore st c
  | .held scId, st, tid, c, rid, ct, rt, _ =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid)) ∧ tid.isReserved = false ∧
      replyHeldPopsInPlace st c ct.scBindingScCode tid rid = true ∧ rt.scBindingOwnerCode = 0 ∧
      enqueueAdmits rt = true ∧ scId = ⟨replyHeadContextCode st rid - 1⟩
  | .unheld scId home, st, tid, c, rid, ct, rt, _ =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 none) ∧
      replyUnheldPopsInPlace st c rid = true ∧ tid ≠ c ∧ receiveBlockAdmits rt = true ∧
      scId = ⟨replyHeadContextCode st rid - 1⟩ ∧ home = determineTargetCore st c
  | .unlinked, st, tid, c, rid, ct, rt, _ =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 none) ∧
      replyUnlinkedInPlace st c rid = true ∧ tid ≠ c ∧ receiveBlockAdmits rt = true

/-- Every arm's guard names a server other than the caller, on a table that
needs no resize. -/
theorem Admits.facts {arm : ReplyRecvArm} {st : SystemState} {tid c : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {ct rt : TCB} {rp : Reply} (h : arm.Admits st tid c rid ct rt rp)
    (hT : st.objects[c.toObjId]? = some (.tcb ct)) :
    tid ≠ c ∧ st.objects.noResizeDue := by
  cases arm with
  | rendezvous => exact ⟨h.2.2.1, replyWakesInPlace_noResizeDue h.2.1⟩
  | donated scId home =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hNe, hNo, _⟩ :=
      replyPopsInPlace_donation st c tid rid IpcMessage.empty ct hT h.2.1 h.2.2.1
    exact ⟨fun e => hNe e.symm, hNo⟩
  | held scId =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hNe, hNo, _⟩ :=
      replyHeldPopsInPlace_pop st c tid rid IpcMessage.empty ct hT h.2.2.1
    exact ⟨fun e => hNe e.symm, hNo⟩
  | unheld scId home =>
    obtain ⟨_, _, _, _, _, _, hNo, _⟩ :=
      replyUnheldPopsInPlace_pop st c rid IpcMessage.empty ct hT h.2.1
    exact ⟨h.2.2.1, hNo⟩
  | unlinked =>
    have hW : replyWakesInPlace st c ct rid = true := h.2.1
    exact ⟨h.2.2.1, replyWakesInPlace_noResizeDue hW⟩

end ReplyRecvArm

/-- **The blocking reply-receive in place, over every arm**: under the arm's
guard and the checks every arm shares, the composite answering the caller with
`answer` is the arm's reply leg, its pop and the receive's tail, the caller then
answered, the server left blocked on the endpoint.  One equality per arm, each
the arm's own (`replyRecvAnsweringOnCore_blocks_inPlace`,
`replyRecvAnsweringOnCore_donated_inPlace`, `replyRecvAnsweringOnCore_held_inPlace`,
`replyRecvAnsweringOnCore_unheld_inPlace`, `replyRecvAnsweringOnCore_unlinked_inPlace`). -/
theorem replyRecvAnsweringOnCore_arm_inPlace (arm : ReplyRecvArm)
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (hAd : arm.Admits st tid c rid ct rt rp)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : answer = none → replyTransferInert st tid ct grant = true) :
    endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
      .ok ({ results := #[] }, replyRecvAnswerCaller answer
        (arm.tail (arm.pop (arm.leg st c tid rid msg) c tid) tid rid epId ep.recvTailCode core)
        c 0) ∧
      ∃ x, (ReplyRecvArm.blocked (arm.pop (arm.leg st c tid rid msg) c tid) tid rid epId
          ep.recvTailCode core).getTcb? tid = some x ∧ x.ipcState = .blockedOnReceive epId := by
  cases arm with
  | rendezvous =>
    obtain ⟨⟨ep0, hIpc⟩, hG, hNe, hA, hFree⟩ := hAd
    refine ⟨replyRecvAnsweringOnCore_blocks_inPlace answer st epId tid c rid msg grant core ct ep0
      rt ep rp hSz hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hFree hStash hRec hInert, ?_⟩
    have hNo := replyWakesInPlace_noResizeDue hG
    have hFC : st.objects.findsInPlace c.toObjId = true := by
      simp only [replyWakesInPlace, Bool.and_eq_true] at hG
      exact hG.1.1.1.2
    obtain ⟨hE0, ⟨rt0, hR0, hA0, -⟩, hG0⟩ := storeReplyRendezvous_receiveGuard st c tid rid msg ct
      rp epId ep rt hNo hT hFC hRp hNe hE hR hA hEnq hFree hStash hRec
    obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := receiveReturnSchedContext_receiveGuard true _ tid
      (storeReplyRendezvous_noResizeDue st c tid rid msg hNo) hE0 hR0 hA0 hG0
    exact receiveBlock_receiver_blocked _ epId ep tid rt1 (some rid) core hE1 hR1 hA1 hG1
  | donated scId home =>
    obtain ⟨⟨ep0, hIpc⟩, hSRes, hG, hA, rfl, rfl⟩ := hAd
    exact replyRecvAnsweringOnCore_donated_inPlace answer st epId tid c rid msg grant core ct ep0
      rt ep rp hSz hT hIpc hRO hSRes hG hE hS hR hA hEnq hRp hStash hRec hInert
  | held scId =>
    obtain ⟨⟨ep0, hIpc⟩, hSRes, hG, hOwn, hA, rfl⟩ := hAd
    exact replyRecvAnsweringOnCore_held_inPlace answer st epId tid c rid msg grant core ct ep0
      rt ep rp hSz hT hIpc hRO hSRes hG hE hS hR hOwn hA hEnq hRp hStash hRec hInert
  | unheld scId home =>
    obtain ⟨⟨ep0, hIpc⟩, hG, hNe, hA, rfl, rfl⟩ := hAd
    exact replyRecvAnsweringOnCore_unheld_inPlace answer st epId tid c rid msg grant core ct ep0
      rt ep rp hSz hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hStash hRec hInert
  | unlinked =>
    obtain ⟨⟨ep0, hIpc⟩, hG, hNe, hA⟩ := hAd
    exact replyRecvAnsweringOnCore_unlinked_inPlace answer st epId tid c rid msg grant core ct ep0
      rt ep rp hSz hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hStash hRec hInert

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-! ### The short message -/

/-- **The blocking reply-receive, delivered in the registers, over every arm**:
the arm's writes in place (`ReplyRecvArm.ready`), then the reply's frame
written into the caller's saved registers.  The message is built only where the
caller is, unexpectedly, not ready. -/
@[noinline] def performReplyRecvArmDelivered (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId) : SystemState :=
  let X := arm.ready st c tid rid epId tailCode core
  writeDeliveredFrameIfReady X c (Architecture.regMessageFrame layout rf len badge)
    (fun _ => holdReplyRecvBody X c layout rf len badge)

/-- The arm's writes, the caller then holding `msg`, are the specification's
reply leg, pop and tail. -/
theorem ReplyRecvArm.tail_pop_leg (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (core : CoreId) (hNo : st.objects.noResizeDue) (hNe : tid ≠ c) :
    arm.tail (arm.pop (arm.leg st c tid rid msg) c tid) tid rid epId tailCode core =
      (arm.ready st c tid rid epId tailCode core).mapTcbInPlace c (holdMessage msg) := by
  have h1 := arm.legReady_noResizeDue st c tid rid hNo
  rw [arm.leg_eq_hold st c tid rid msg hNo, arm.pop_msg c id (fun _ => some msg) id _ c tid h1
      (fun e => hNe e.symm),
    arm.tail_msg c msg _ tid rid epId tailCode core (arm.pop_noResizeDue _ c tid h1)
      (fun e => hNe e.symm)]
  unfold ReplyRecvArm.ready
  rw [ReplyRecvArm.tailFast_eq]

/-- The server the arm's writes leave is blocked on the endpoint. -/
theorem ReplyRecvArm.ready_blocked (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (core : CoreId) (hNo : st.objects.noResizeDue) (hNe : tid ≠ c) {x : TCB}
    (hX : (ReplyRecvArm.blocked (arm.pop (arm.leg st c tid rid msg) c tid) tid rid epId tailCode
      core).getTcb? tid = some x) :
    ∃ x', (arm.ready st c tid rid epId tailCode core).getTcb? tid = some x' ∧
      x'.ipcState = x.ipcState := by
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have h1 := arm.legReady_noResizeDue st c tid rid hNo
  have h2 := arm.pop_noResizeDue _ c tid h1
  rw [arm.leg_eq_hold st c tid rid msg hNo, arm.pop_msg c id (fun _ => some msg) id _ c tid h1
      (fun e => hNe e.symm), ReplyRecvArm.blocked_msg c msg _ tid rid epId tailCode core h2
      (fun e => hNe e.symm), SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hX
  have h3 := ReplyRecvArm.blocked_noResizeDue _ tid rid epId tailCode core h2
  obtain ⟨x1, hX1, e1⟩ := arm.desched_ipcStateCarried _ tid tid x hX
  obtain ⟨x2, hX2, e2⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core
    (arm.desched_noResizeDue _ tid h3) tid x1 hX1
  refine ⟨x2, ?_, e2.trans e1⟩
  unfold ReplyRecvArm.ready
  rw [ReplyRecvArm.tailFast_eq]
  exact hX2

/-- **The blocking reply-receive, delivered, over every arm**: under the arm's
guard and a reply of at most four words, the checked arm's result is the
caller's frame written into its saved registers on top of the arm's writes; the
server, blocked on the endpoint, stages nothing. -/
theorem replyRecvOnCore_arm_delivered (arm : ReplyRecvArm) (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (grant : Bool) (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (hAd : arm.Admits st tid c rid ct rt rp)
    (hSz : ¬ msg.registers.size > maxMessageRegisters) (hSz4 : msg.registers.size ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : replyTransferInert st tid ct grant = true) :
    (match endpointReplyRecvOnCore epId tid rid c msg grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), writeDeliveredFrameIfReady (arm.ready st c tid rid epId ep.recvTailCode core) c
        (Architecture.returnFrameOfMessage msg 0 0)
        (fun _ => (arm.ready st c tid rid epId ep.recvTailCode core).mapTcbInPlace c
          (holdMessage msg))) := by
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_arm_inPlace arm none st epId tid c rid msg
    grant core ct rt ep rp hAd hSz hT hRO hE hS hR hEnq hRp hStash hRec (fun _ => hInert)
  obtain ⟨x', hX', hB'⟩ := arm.ready_blocked st c tid rid msg epId ep.recvTailCode core hNo hNe hX
  unfold endpointReplyRecvOnCore
  rw [hEq]
  simp only [CapTransferSummary.capInfo_empty, replyRecvAnswerCaller]
  have h1 := arm.legReady_noResizeDue st c tid rid hNo
  have hNoX : (arm.ready st c tid rid epId ep.recvTailCode core).objects.noResizeDue := by
    unfold ReplyRecvArm.ready
    rw [ReplyRecvArm.tailFast_eq]
    exact arm.tail_noResizeDue _ tid rid epId _ core (arm.pop_noResizeDue _ c tid h1)
  rw [arm.tail_pop_leg st c tid rid msg epId ep.recvTailCode core hNo hNe,
    stageDeliveredMessage_holdMessage _ _ _ hNoX hSz4,
    stageDeliveredMessage_writeDeliveredFrameIfReady_blocked _ c tid _ _ 0 hCT x' hX'
      (by rw [hB', hB]; exact fun h => by cases h)]

/-! ### The long message -/

/-- **The receive tail stages the caller's held long message as the long
frame**, the server it blocks staging nothing: on a state `Y` the arm's pop
leaves, staging the caller holding the long message read in `Z` and then the
server is the long frame on the arm's tail, its overflow words read in that
state, which reads every buffer as `Z` does (`hW`). -/
theorem ReplyRecvArm.tail_stagedLong (arm : ReplyRecvArm) (Y Z : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (core : CoreId) (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (capInfo : Nat) (hNo : Y.objects.noResizeDue) (hNe : tid ≠ c) (hLen : 5 ≤ len)
    (hW : ipcWordReadsAgree (arm.tail Y tid rid epId tailCode core) Z)
    (hB : ∃ x, (ReplyRecvArm.blocked (Y.mapTcbInPlace c (holdMessage
        { registers := longReplyRecvRegs rf Z tid len, badge := badge })) tid rid epId tailCode
        core).getTcb? tid = some x ∧ x.ipcState = .blockedOnReceive epId) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
        (arm.tail (Y.mapTcbInPlace c (holdMessage
          { registers := longReplyRecvRegs rf Z tid len, badge := badge })) tid rid epId tailCode
          core) c capInfo) tid 0 =
      deliverLongReplyRecvCapsFrame capInfo (arm.tail Y tid rid epId tailCode core) c rf len tid
        badge := by
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨t, hT1, hBk⟩ := hB
  have h3 := ReplyRecvArm.blocked_noResizeDue Y tid rid epId tailCode core hNo
  rw [ReplyRecvArm.blocked_msg c _ Y tid rid epId tailCode core hNo (fun e => hNe e.symm),
    SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hT1
  obtain ⟨x1, hX1, e1⟩ := arm.desched_ipcStateCarried _ tid tid t hT1
  obtain ⟨x, hX, hEq⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core
    (arm.desched_noResizeDue _ tid h3) tid x1 hX1
  rw [arm.tail_msg c _ Y tid rid epId tailCode core hNo (fun e => hNe e.symm),
    ← deliverLongReplyRecvFrame_eq _ Z c tid rf len badge capInfo
      (arm.tail_noResizeDue Y tid rid epId tailCode core hNo) hW (by omega)]
  unfold deliverLongReplyRecvCapsFrame
  exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x
    (by rw [deliverLongReplyRecvFrame_getTcb?_ne _ _ _ _ _ _ _ _ hCT]; exact hX)
    (by rw [hEq, e1, hBk]; exact fun h => by cases h)

/-- **The long blocking reply-receive, its reply transferring nothing,
delivered over every arm**: the arm's writes in place, then the long frame. -/
@[noinline] def performReplyRecvArmDeliveredLong (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (core : CoreId) :
    SystemState :=
  deliverLongReplyRecvCapsFrame 0 (arm.ready st c tid rid epId tailCode core) c rf len tid badge

/-- **The long blocking reply-receive, delivered, over every arm**: under the
arm's guard and a message of `len` words, more than four, the checked arm's
result is `performReplyRecvArmDeliveredLong`.  The held arm's long reply is
answered in place here for the first time. -/
theorem replyRecvOnCore_arm_deliveredLong (arm : ReplyRecvArm) (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (hAd : arm.Admits st tid c rid ct rt rp)
    (hLen : 5 ≤ len) (hSz : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : replyTransferInert st tid ct grant = true) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmDeliveredLong arm st c tid rid epId ep.recvTailCode rf len badge
        core) := by
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_arm_inPlace arm none st epId tid c rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core ct rt ep rp hAd hSz
    hT hRO hE hS hR hEnq hRp hStash hRec (fun _ => hInert)
  unfold endpointReplyRecvOnCore
  rw [hEq]
  simp only [CapTransferSummary.capInfo_empty, replyRecvAnswerCaller]
  have h1 := arm.legReady_noResizeDue st c tid rid hNo
  have hNoP := arm.pop_noResizeDue _ c tid h1
  have hAP := (arm.ipcBufferReadsAgree_pop _ c tid h1).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)
  rw [arm.leg_eq_hold st c tid rid _ hNo, arm.pop_msg c id _ id _ c tid h1
    (fun e => hNe e.symm)] at hX ⊢
  unfold performReplyRecvArmDeliveredLong ReplyRecvArm.ready
  rw [ReplyRecvArm.tailFast_eq]
  exact congrArg (fun Z => (.ok ((), Z) : Except KernelError (Unit × SystemState)))
    (arm.tail_stagedLong _ st c tid rid epId ep.recvTailCode core rf len badge 0 hNoP hNe hLen
      ((arm.ipcBufferReadsAgree_tail _ tid rid epId ep.recvTailCode core hNoP).words.trans
        hAP.words) ⟨x, hX, hB⟩)

/-! ### The fault answer -/

/-- The reply leg of a fault answer: the reply's writes with no message. -/
@[inline] def ReplyRecvArm.faultLeg (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : SystemState :=
  if arm.recordsServer then storeFaultReplyRendezvous st c tid rid else storeFaultReplyLeg st c rid

theorem ReplyRecvArm.faultLeg_eq (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) :
    arm.faultLeg st c tid rid = arm.leg st c tid rid IpcMessage.empty := by
  unfold ReplyRecvArm.faultLeg ReplyRecvArm.leg
  split <;> rfl

theorem ReplyRecvArm.ipcBufferReadsAgree_leg (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (hNo : st.objects.noResizeDue) : ipcBufferReadsAgree (arm.leg st c tid rid msg) st := by
  rw [arm.leg_eq_hold st c tid rid msg hNo]
  exact (ipcBufferReadsAgree_mapTcbInPlace _ c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)

/-- The arm's writes after a fault answer's reply leg, in place. -/
@[inline] def ReplyRecvArm.faultReady (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (core : CoreId) : SystemState :=
  arm.tailFast (arm.pop (arm.faultLeg st c tid rid) c tid) tid rid epId tailCode core

theorem ReplyRecvArm.faultReady_eq (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (core : CoreId) :
    arm.faultReady st c tid rid epId tailCode core =
      arm.tail (arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid) tid rid epId tailCode
        core := by
  unfold ReplyRecvArm.faultReady
  rw [arm.faultLeg_eq, ReplyRecvArm.tailFast_eq]

/-- The server the fault answer's writes leave blocked, as the arm's guard
reads it. -/
theorem ReplyRecvArm.faultReady_blocked (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (core : CoreId) (hNo : st.objects.noResizeDue) {x : TCB}
    (hX : (ReplyRecvArm.blocked (arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid) tid rid
      epId tailCode core).getTcb? tid = some x) :
    ∃ x', (arm.faultReady st c tid rid epId tailCode core).getTcb? tid = some x' ∧
      x'.ipcState = x.ipcState ∧
      (arm.faultReady st c tid rid epId tailCode core).objects.noResizeDue := by
  have h2 := arm.pop_noResizeDue _ c tid (arm.leg_noResizeDue st c tid rid IpcMessage.empty hNo)
  have h3 := ReplyRecvArm.blocked_noResizeDue _ tid rid epId tailCode core h2
  obtain ⟨x1, hX1, e1⟩ := arm.desched_ipcStateCarried _ tid tid x hX
  obtain ⟨x2, hX2, e2⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core
    (arm.desched_noResizeDue _ tid h3) tid x1 hX1
  rw [arm.faultReady_eq]
  exact ⟨x2, hX2, e2.trans e1, arm.tail_noResizeDue _ tid rid epId tailCode core h2⟩

/-- **The blocking reply-receive answering a fault, over every arm**: the
reply's writes with no message, the arm's pop, the receive's tail, then the
fault answer (`performFaultAnswer`). -/
@[noinline] def performReplyRecvArmFaultAnswer (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (core : CoreId) (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat) :
    SystemState :=
  performFaultAnswer (arm.faultReady st c tid rid epId tailCode core) c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf (Architecture.regMessageLength layout len) 0

/-- **The blocking reply-receive answering a fault is the specification's, over
every arm**, and it stages nothing for the server, which the receive leaves
blocked.  The held arm's fault is answered in place here for the first time. -/
theorem replyRecvTransferOnCore_arm_fault_inPlace (arm : ReplyRecvArm) (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (grant : Bool) (core : CoreId)
    (ct rt : TCB) (ep : Endpoint) (rp : Reply) (tf : ThreadFault)
    (hAd : arm.Admits st tid c rid ct rt rp)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    replyRecvTransferOnCore epId tid rid c label
        { registers := Architecture.regMessageBody layout rf len, badge := badge }
        grant core st =
      .ok ({ results := #[] }, performReplyRecvArmFaultAnswer arm st c tid rid epId
        ep.recvTailCode core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf
        len) ∧
    Architecture.stageDeliveredMessage (performReplyRecvArmFaultAnswer arm st c tid rid epId
        ep.recvTailCode core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf
        len) tid 0 =
      performReplyRecvArmFaultAnswer arm st c tid rid epId ep.recvTailCode core ct.faultKind
        label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3
        ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf len := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_arm_inPlace arm
    (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regMessageBody layout rf len, badge := badge })
    st epId tid c rid IpcMessage.empty grant core ct rt ep rp hAd (by simp [IpcMessage.empty])
    hT hRO hE hS hR hEnq hRp hStash hRec
    (fun h => by rw [replyRecvCallerFaultAnswer?_of_fault st c ct tf label _ hTc hPF] at h; cases h)
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label
    { registers := Architecture.regMessageBody layout rf len, badge := badge } hTc hPF
  have hAp : ∀ X : SystemState, replyRecvAnswerCaller
        (replyRecvCallerFaultAnswer? st c label
          { registers := Architecture.regMessageBody layout rf len, badge := badge }) X c 0 =
      performFaultAnswer X c ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf
        (Architecture.regMessageLength layout len) 0 := fun X => by
    rw [hAns]
    exact faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF _ _ layout rf
      (Architecture.regMessageLength layout len) 0
      (by simp only [Architecture.regMessageBody_size, Nat.min_self])
      (fun i hi => wordAt_regMessageBody layout rf len i hi)
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regMessageBody layout rf len, badge := badge })
      { registers := Architecture.regMessageBody layout rf len, badge := badge } =
      IpcMessage.empty := by rw [hAns]; rfl
  refine ⟨?_, ?_⟩
  · unfold replyRecvTransferOnCore performReplyRecvArmFaultAnswer
    rw [hL, hEq, hAp, arm.faultReady_eq]
  · obtain ⟨x', hX', e', hNoF⟩ := arm.faultReady_blocked st c tid rid epId ep.recvTailCode core
      hNo hX
    obtain ⟨x3, hX3, e3⟩ := performFaultAnswer_ipcStateAt _ c tid ct.faultKind label ct.faultIp
      ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
      ct.faultX6 ct.faultX7 layout rf (Architecture.regMessageLength layout len) 0 hCT hNoF x' hX'
    unfold performReplyRecvArmFaultAnswer
    exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x3 hX3
      (by rw [e3, e', hB]; exact fun h => by cases h)

/-- **The long blocking reply-receive answering a fault, over every arm**: as
`performReplyRecvArmFaultAnswer`, the reply's words past MR3 read from the
replier's buffer (`performFaultAnswerLong`). -/
@[noinline] def performReplyRecvArmFaultAnswerLong (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (core : CoreId) (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (rf : SeLe4n.RegisterFile) (len : Nat) : SystemState :=
  performFaultAnswerLong (arm.faultReady st c tid rid epId tailCode core) c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 tid rf len

/-- **The long blocking reply-receive answering a fault is the
specification's, over every arm**, and it stages nothing for the server. -/
theorem replyRecvTransferOnCore_arm_fault_inPlaceLong (arm : ReplyRecvArm) (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply) (tf : ThreadFault)
    (hAd : arm.Admits st tid c rid ct rt rp) (hLen : 4 ≤ len)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    replyRecvTransferOnCore epId tid rid c label
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st =
      .ok ({ results := #[] }, performReplyRecvArmFaultAnswerLong arm st c tid rid epId
        ep.recvTailCode core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len) ∧
    Architecture.stageDeliveredMessage (performReplyRecvArmFaultAnswerLong arm st c tid rid epId
        ep.recvTailCode core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len)
        tid 0 =
      performReplyRecvArmFaultAnswerLong arm st c tid rid epId ep.recvTailCode core ct.faultKind
        label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3
        ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  let msg : IpcMessage := { registers := longReplyRecvRegs rf st tid len, badge := badge }
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_arm_inPlace arm
    (replyRecvCallerFaultAnswer? st c label msg)
    st epId tid c rid IpcMessage.empty grant core ct rt ep rp hAd (by simp [IpcMessage.empty])
    hT hRO hE hS hR hEnq hRp hStash hRec
    (fun h => by rw [replyRecvCallerFaultAnswer?_of_fault st c ct tf label _ hTc hPF] at h; cases h)
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label msg hTc hPF
  have hNoL := arm.leg_noResizeDue st c tid rid IpcMessage.empty hNo
  have hNoP := arm.pop_noResizeDue _ c tid hNoL
  have hW : ipcWordReadsAgree (arm.tail (arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid)
      tid rid epId ep.recvTailCode core) st :=
    ((arm.ipcBufferReadsAgree_tail _ tid rid epId ep.recvTailCode core hNoP).trans
      ((arm.ipcBufferReadsAgree_pop _ c tid hNoL).trans
        (arm.ipcBufferReadsAgree_leg st c tid rid IpcMessage.empty hNo))).words
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label msg) msg =
      IpcMessage.empty := by rw [hAns]; rfl
  refine ⟨?_, ?_⟩
  · unfold replyRecvTransferOnCore
    rw [hL, hEq]
    unfold performReplyRecvArmFaultAnswerLong replyRecvAnswerCaller
    rw [hAns, arm.faultReady_eq]
    dsimp only
    rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ tid rf len
      (replyWordOr_longReplyRecvRegs st _ tid rf len label hLen hW)]
  · obtain ⟨x', hX', e', hNoF⟩ := arm.faultReady_blocked st c tid rid epId ep.recvTailCode core
      hNo hX
    obtain ⟨x3, hX3, e3⟩ := performFaultAnswerLong_ipcStateAt _ c tid ct.faultKind label
      ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
      ct.faultX5 ct.faultX6 ct.faultX7 tid rf len hCT hNoF x' hX'
    unfold performReplyRecvArmFaultAnswerLong
    exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x3 hX3
      (by rw [e3, e', hB]; exact fun h => by cases h)

/-! ### The capability transfer -/

/-- **The held reply-receive that blocks, its reply leg transferring**: as
`replyRecvAnsweringOnCore_held_inPlace`, with the reply leg's transfer
answering `(summary, S2)` on the state the held pop leaves and the receive's
block admissible on `S2`. -/
theorem replyRecvOnCore_held_transfer (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyHeldPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hS : ep.sendQ.head = none)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyTransferCaps st tid c grant
      (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
        ⟨replyHeadContextCode st rid - 1⟩) = .ok (summary, S2))
    (hE2 : S2.objects[epId]? = some (.endpoint ep)) {rt2 : TCB}
    (hR2 : S2.objects[tid.toObjId]? = some (.tcb rt2)) (hA2 : receiveBlockAdmits rt2 = true)
    (hNo2 : S2.objects.noResizeDue)
    (hG2 : receiveBlocksInPlace S2 epId tid ep.receiveQ.tail (some rid) = true) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock (receiveReturnSchedContext true S2 tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c
            summary.capInfo) := by
  obtain ⟨rp', scId, sc, _, hRp', hN, _, _, _, hCode, hCRes, _, _, hNo, _, _, hLC, hFC,
    hLR, hFR, _, hPop⟩ := replyHeldPopsInPlace_pop st c tid rid msg ct hT hG
  rw [hRp] at hRp'
  cases hRp'
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc] at hXf
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st tid c tid ct ep0 rid rp msg core hSz hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRecS : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  rw [← storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hPop
  generalize hS1 : storeReplyRendezvous st c tid rid msg = S1 at hEq hPop hXf
  generalize hP : keepDonatedSchedContextInPlace S1 tid scId = P at hPop hXf
  have hXf' : replyRecvReplyTransfer none st tid c grant P = .ok (summary, S2) := hXf
  obtain ⟨hE3, ⟨rt3, hR3, hA3⟩, hG3⟩ := receiveReturnSchedContext_receiveGuard true S2 tid hNo2
    hE2 hR2 hA2 hG2
  generalize hQ : receiveReturnSchedContext true S2 tid = Q at hE3 hR3 hG3 ⊢
  have hEp2 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE3
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
      (removeRunnableOnCore (storeReceiveBlock Q epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq Q epId ep tid rt3 (some rid) core hE3 hS hR3 hA3 hG3]
    have hSnd : (receiveRendezvousSender? Q epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp2, hS]
    simp only [hSnd, ↓reduceIte]
  obtain ⟨tb, hTb, hBk⟩ := receiveBlock_receiver_blocked Q epId ep tid rt3 (some rid) core hE3 hR3
    hA3 hG3
  have hDq : rendezvousDequeuedCall (removeRunnableOnCore (storeReceiveBlock Q epId tid
      ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid = false := by
    unfold rendezvousDequeuedCall lookupTcb
    simp only [hSRes, Bool.false_eq_true, ↓reduceIte, hTb, hBk]
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_some, hEq, hPop, hXf', hQ, hRecv]
  simp [replyRecvPostReceiveDonation, hDq, applyReceiveLegPipHandoff, replyRecvAnswerCaller]

/-- **The blocking reply-receive whose reply leg transfers, over every arm**:
with the reply leg's transfer answering `(summary, S2)` on the state the arm's
pop leaves and the receive's block admissible on `S2`, the composite is the
arm's tail on `S2` and the caller staged with the transfer's report. -/
theorem replyRecvOnCore_arm_transfer (arm : ReplyRecvArm) (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (grant : Bool) (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (hAd : arm.Admits st tid c rid ct rt rp)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hS : ep.sendQ.head = none)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyTransferCaps st tid c grant (arm.pop (arm.leg st c tid rid msg) c tid) =
      .ok (summary, S2))
    (hE2 : S2.objects[epId]? = some (.endpoint ep)) {rt2 : TCB}
    (hR2 : S2.objects[tid.toObjId]? = some (.tcb rt2)) (hA2 : receiveBlockAdmits rt2 = true)
    (hNo2 : S2.objects.noResizeDue)
    (hG2 : receiveBlocksInPlace S2 epId tid ep.receiveQ.tail (some rid) = true) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (arm.tail S2 tid rid epId ep.recvTailCode core) c summary.capInfo) := by
  cases arm with
  | rendezvous =>
    obtain ⟨⟨ep0, hIpc⟩, hG, -, -, -⟩ := hAd
    exact replyRecvOnCore_blocks_transfer st epId tid c rid msg grant core ct ep0 ep hSz hT hIpc
      hRO hG hS hXf hE2 hR2 hA2 hNo2 hG2
  | donated scId home =>
    obtain ⟨⟨ep0, hIpc⟩, hSRes, hG, -, rfl, rfl⟩ := hAd
    exact replyRecvOnCore_donated_transfer st epId tid c rid msg grant core ct ep0 ep rp hSz hT hIpc
      hRO hSRes hG hS hRp hXf hE2 hR2 hA2 hNo2 hG2
  | held scId =>
    obtain ⟨⟨ep0, hIpc⟩, hSRes, hG, -, -, rfl⟩ := hAd
    exact replyRecvOnCore_held_transfer st epId tid c rid msg grant core ct ep0 ep rp hSz hT hIpc
      hRO hSRes hG hS hRp hXf hE2 hR2 hA2 hNo2 hG2
  | unheld scId home =>
    obtain ⟨⟨ep0, hIpc⟩, hG, -, -, rfl, rfl⟩ := hAd
    exact replyRecvOnCore_unheld_transfer st epId tid c rid msg grant core ct ep0 ep rp hSz hT hIpc
      hRO hG hS hRp hXf hE2 hR2 hA2 hNo2 hG2
  | unlinked =>
    obtain ⟨⟨ep0, hIpc⟩, hG, -, -⟩ := hAd
    exact replyRecvOnCore_unlinked_transfer st epId tid c rid msg grant core ct ep0 ep rp hSz hT
      hIpc hRO hG hS hRp hXf hE2 hR2 hA2 hNo2 hG2

/-- **The reply leg and the arm's pop carry the receive's guard**: on the state
they leave, the endpoint is as it was, the server may block on it and its block
writes in place, each read on the pre-state.  Per arm, the arm's own carry
(`storeReplyRendezvous_receiveGuard`, `popDonationSettled_receiveGuard`,
`keepHeldPop_receiveGuard`, `popUnheldSettled_receiveGuard`,
`storeReplyLeg_receiveGuard`). -/
theorem ReplyRecvArm.receiveGuard (arm : ReplyRecvArm) (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (hAd : arm.Admits st tid c rid ct rt rp)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    (arm.pop (arm.leg st c tid rid msg) c tid).objects[epId]? = some (.endpoint ep) ∧
      (∃ rt1, (arm.pop (arm.leg st c tid rid msg) c tid).objects[tid.toObjId]? =
          some (.tcb rt1) ∧ receiveBlockAdmits rt1 = true ∧
          rt1.boundNotificationCode = rt.boundNotificationCode) ∧
      receiveBlocksInPlace (arm.pop (arm.leg st c tid rid msg) c tid) epId tid ep.receiveQ.tail
        (some rid) = true := by
  cases arm with
  | rendezvous =>
    obtain ⟨-, hG, hNe, hA, hFree⟩ := hAd
    have hNo := replyWakesInPlace_noResizeDue hG
    have hFC : st.objects.findsInPlace c.toObjId = true := by
      simp only [replyWakesInPlace, Bool.and_eq_true] at hG
      exact hG.1.1.1.2
    exact storeReplyRendezvous_receiveGuard st c tid rid msg ct rp epId ep rt hNo hT hFC hRp hNe
      hE hR hA hEnq hFree hStash hRec
  | donated scId home =>
    obtain ⟨-, hSRes, hG, hA, rfl, rfl⟩ := hAd
    obtain ⟨rp', scId', sc, hRp', hN, hScO, hHead, hBelow, hCode, -, hNe', hNo, -, hFC, -⟩ :=
      replyPopsInPlace_donation st c tid rid msg ct hT hSRes hG
    rw [hRp] at hRp'
    cases hRp'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId' := by
      rw [hCode]; rfl
    show (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid _ _).objects[epId]? =
      _ ∧ _
    rw [hSc]
    exact popDonationSettled_receiveGuard st c tid rid msg ct rp epId ep rt scId' sc _ hNo hT hFC
      hRp hN hScO hHead hBelow (fun e => hNe' e.symm) hE hR hA hEnq hStash hRec
  | held scId =>
    obtain ⟨-, -, hG, hOwn, hA, rfl⟩ := hAd
    obtain ⟨rp', scId', sc, _, hRp', hN, hScO, hHead, hBelow, hCode, -, -, hNe', hNo, -, -, -, hFC,
      -⟩ := replyHeldPopsInPlace_pop st c tid rid msg ct hT hG
    rw [hRp] at hRp'
    cases hRp'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId' := by
      rw [hCode]; rfl
    show (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid _).objects[epId]?
      = _ ∧ _
    rw [hSc]
    exact keepHeldPop_receiveGuard st c tid rid msg ct rp epId ep rt scId' sc hNo hT hFC hRp hN hScO
      hHead hBelow (fun e => hNe' e.symm) hE hR hOwn hA hEnq hStash hRec
  | unheld scId home =>
    obtain ⟨-, hG, hNe, hA, rfl, rfl⟩ := hAd
    obtain ⟨rp', scId', hRp', hN, hCode, -, hNo, -, hFC, -⟩ :=
      replyUnheldPopsInPlace_pop st c rid msg ct hT hG
    obtain ⟨rp'', scId'', sc, hRp'', hN', hScO, hHead, hBelow⟩ := replyUnheldPopsInPlace_stack st c rid hG
    rw [hRp] at hRp' hRp''
    cases hRp'
    cases hRp''
    rw [hN] at hN'
    cases hN'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId' := by
      rw [hCode]; rfl
    show (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
      (storeReplyLeg st c rid msg) c _) _ _).objects[epId]? = _ ∧ _
    rw [hSc]
    exact popUnheldSettled_receiveGuard st c tid rid msg ct rp epId ep rt scId' sc _ hNo hT hFC hRp
      hN hScO hHead hBelow hNe hE hR hA hEnq hStash hRec
  | unlinked =>
    obtain ⟨-, hG, hNe, hA⟩ := hAd
    have hW : replyWakesInPlace st c ct rid = true := hG
    exact storeReplyLeg_receiveGuard st c tid rid msg ct rp epId ep rt
      (replyWakesInPlace_noResizeDue hW) hT (replyUnlinkedInPlace_findsCaller hG) hRp hNe hE hR hA
      hEnq (replyUnlinkedInPlace_consumedFree hG hRp) hStash hRec

/-! ### The capability answer -/

/-- **The receive tail stages the caller's held reply and the transfer's report
as the caller's frame**, the server it blocks staging nothing: on a state `Y`
the reply's transfer leaves, the receive's block admissible on `Y` with the
caller holding the reply. -/
theorem ReplyRecvArm.tail_staged (arm : ReplyRecvArm) (Y : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (ep : Endpoint) (core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (hNo : Y.objects.noResizeDue) (hNe : tid ≠ c)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hE2 : (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regMessageBody layout rf len, badge := badge })).objects[epId]? =
        some (.endpoint ep)) {rt2 : TCB}
    (hR2 : (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regMessageBody layout rf len, badge := badge })).objects[tid.toObjId]? =
        some (.tcb rt2))
    (hA2 : receiveBlockAdmits rt2 = true)
    (hG2 : receiveBlocksInPlace (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regMessageBody layout rf len, badge := badge })) epId tid
        ep.receiveQ.tail (some rid) = true) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
        (arm.tail (Y.mapTcbInPlace c (holdMessage
          { registers := Architecture.regMessageBody layout rf len, badge := badge })) tid rid epId
          ep.recvTailCode core) c capInfo) tid 0 =
      deliverReplyRecvCapsFrame capInfo (arm.tailFast Y tid rid epId ep.recvTailCode core) c layout
        rf len badge := by
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨hE3, ⟨rt3, hR3, hA3⟩, hG3⟩ := receiveReturnSchedContext_receiveGuard true _ tid
    ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNo) hE2 hR2 hA2 hG2
  obtain ⟨t, hT0, hBk⟩ := receiveBlock_receiver_blocked _ epId ep tid rt3 (some rid) core hE3 hR3
    hA3 hG3
  have hT1 : (ReplyRecvArm.blocked (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regMessageBody layout rf len, badge := badge })) tid rid epId
      ep.recvTailCode core).getTcb? tid = some t := hT0
  have h3 := ReplyRecvArm.blocked_noResizeDue Y tid rid epId ep.recvTailCode core hNo
  rw [ReplyRecvArm.blocked_msg c _ Y tid rid epId _ core hNo (fun e => hNe e.symm),
    SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hT1
  obtain ⟨x1, hX1, e1⟩ := arm.desched_ipcStateCarried _ tid tid t hT1
  obtain ⟨x, hX, hEq⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core
    (arm.desched_noResizeDue _ tid h3) tid x1 hX1
  have hX' : (arm.tailFast Y tid rid epId ep.recvTailCode core).getTcb? tid = some x := by
    rw [ReplyRecvArm.tailFast_eq]; exact hX
  rw [arm.tail_msg c _ Y tid rid epId _ core hNo (fun e => hNe e.symm),
    stageDeliveredMessage_holdMessage_caps _ _ _ _ (arm.tail_noResizeDue Y tid rid epId _ core hNo)
      (by rw [Architecture.regMessageBody_size]; exact hSz4),
    returnFrameOfMessage_regMessageBody_capsOpt, ← ReplyRecvArm.tailFast_eq]
  exact stageDeliveredMessage_writeDeliveredFrameIfReady_blocked
    (arm.tailFast Y tid rid epId ep.recvTailCode core) c tid _ _ 0 hCT x hX'
    (by rw [hEq, e1, hBk]; exact fun h => by cases h)

/-- **The blocking reply-receive whose reply leg transfers, delivered, over
every arm**: the arm's reply leg and pop, the transfer in place on no endpoint,
the arm's tail, then the caller's frame with the transfer's report.  The held
arm's capability answer is in place here for the first time. -/
@[noinline] def performReplyRecvArmCapsDelivered (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := arm.pop (arm.legReady st c tid rid) c tid
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverReplyRecvCapsFrame
      (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (arm.tailFast
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
        tid rid epId tailCode core)
      c layout rf len badge

/-- **The blocking reply-receive whose reply leg transfers, delivered, over
every arm**: under the arm's guard, a granting replier whose frame asks for
`count` capabilities and a reply of at most four words, the checked arm's
result is `performReplyRecvArmCapsDelivered`. -/
theorem replyRecvOnCore_arm_capsDelivered (arm : ReplyRecvArm) (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (stcb : TCB) (count : Nat)
    (hAd : arm.Admits st tid c rid ct rt rp)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmCapsDelivered arm st c tid rid epId ep.recvTailCode layout rf len
        badge core stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] count ct.spaceCells[2]
        ct.ipcBuffer ct.spaceCells[0]) := by
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  have hSz : ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regMessageBody_size]; unfold maxMessageRegisters; omega
  generalize hMsg : ({ registers := Architecture.regMessageBody layout rf len, badge := badge } :
    IpcMessage) = msg
  obtain ⟨hE1, ⟨rt1, hR1, hA1, -⟩, hG1⟩ := arm.receiveGuard st epId tid c rid msg ct rt ep rp hAd
    hT hE hR hEnq hRp hStash hRec
  have hNoX := arm.legReady_noResizeDue st c tid rid hNo
  have hP1 : arm.pop (arm.leg st c tid rid msg) c tid =
      (arm.pop (arm.legReady st c tid rid) c tid).mapTcbInPlace c (holdMessage msg) := by
    rw [arm.leg_eq_hold st c tid rid msg hNo]
    exact arm.pop_msg c id _ id _ c tid hNoX (fun e => hNe e.symm)
  have hAP := (arm.ipcBufferReadsAgree_pop _ c tid hNoX).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)
  have hNoP := arm.pop_noResizeDue _ c tid hNoX
  generalize hX : arm.pop (arm.legReady st c tid rid) c tid = X at hP1 hNoP hAP
  rw [hP1] at hE1 hR1 hG1
  obtain ⟨s, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 s hNoP hT1
  have hHT : receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
      (X.mapTcbInPlace c (holdMessage msg)) = .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoP, hT1]
    rfl
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAP)
    ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoP) c.toObjId stcb ct count hHT).1
  obtain ⟨hE2, ⟨rt2, hR2, hA2, -⟩, hG2⟩ := receiveGuard_of_transferFrame hFr hE1 hR1 hA1 hG1
  have hXf : replyTransferCaps st tid c true (arm.pop (arm.leg st c tid rid msg) c tid) =
      .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    unfold replyTransferCaps
    rw [hReq, hTgt, hP1, hHT]
  rw [replyRecvOnCore_arm_transfer arm st epId tid c rid msg true core ct rt ep rp hAd (hMsg ▸ hSz)
    hT hRO hS hRp hXf hE2 hR2 hA2 ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoY) hG2]
  dsimp only
  subst hMsg
  simp only [CapTransferSummary.capInfo_empty]
  rw [arm.tail_staged Y1 c tid rid epId ep core layout rf len badge s.capInfo hNoY hNe hSz4 hE2 hR2
    hA2 hG2]
  have hK := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => deliverReplyRecvCapsFrame i (arm.tailFast Y tid rid epId ep.recvTailCode core) c
      layout rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hK
  rw [hAP.frameCapRequestOf, hAP.capTargetOf, hT1] at hK
  unfold performReplyRecvArmCapsDelivered
  rw [hX]
  exact congrArg (fun Z => (.ok ((), Z) : Except KernelError (Unit × SystemState))) hK.symm

/-- **The long blocking reply-receive whose reply leg transfers, delivered,
over every arm**: as `performReplyRecvArmCapsDelivered`, with the long frame. -/
@[noinline] def performReplyRecvArmCapsDeliveredLong (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (core : CoreId)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := arm.pop (arm.legReady st c tid rid) c tid
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverLongReplyRecvCapsFrame
      (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (arm.tailFast
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
        tid rid epId tailCode core)
      c rf len tid badge

/-- **The long blocking reply-receive whose reply leg transfers, delivered,
over every arm**: as `replyRecvOnCore_arm_capsDelivered`, for a message of
`len` words, more than four, read in the replier's registers and buffer. -/
theorem replyRecvOnCore_arm_capsDeliveredLong (arm : ReplyRecvArm) (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (core : CoreId)
    (ct rt : TCB) (ep : Endpoint) (rp : Reply) (stcb : TCB) (count : Nat)
    (hAd : arm.Admits st tid c rid ct rt rp)
    (hLen : 5 ≤ len) (hSz : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmCapsDeliveredLong arm st c tid rid epId ep.recvTailCode rf len
        badge core stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] count ct.spaceCells[2]
        ct.ipcBuffer ct.spaceCells[0]) := by
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  generalize hMsg : ({ registers := longReplyRecvRegs rf st tid len, badge := badge } :
    IpcMessage) = msg
  obtain ⟨hE1, ⟨rt1, hR1, hA1, -⟩, hG1⟩ := arm.receiveGuard st epId tid c rid msg ct rt ep rp hAd
    hT hE hR hEnq hRp hStash hRec
  have hNoX := arm.legReady_noResizeDue st c tid rid hNo
  have hP1 : arm.pop (arm.leg st c tid rid msg) c tid =
      (arm.pop (arm.legReady st c tid rid) c tid).mapTcbInPlace c (holdMessage msg) := by
    rw [arm.leg_eq_hold st c tid rid msg hNo]
    exact arm.pop_msg c id _ id _ c tid hNoX (fun e => hNe e.symm)
  have hAP := (arm.ipcBufferReadsAgree_pop _ c tid hNoX).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)
  have hNoP := arm.pop_noResizeDue _ c tid hNoX
  generalize hX : arm.pop (arm.legReady st c tid rid) c tid = X at hP1 hNoP hAP
  rw [hP1] at hE1 hR1 hG1
  obtain ⟨s, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 s hNoP hT1
  have hHT : receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
      (X.mapTcbInPlace c (holdMessage msg)) = .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoP, hT1]
    rfl
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAP)
    ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoP) c.toObjId stcb ct count hHT).1
  obtain ⟨hE2, ⟨rt2, hR2, hA2, -⟩, hG2⟩ := receiveGuard_of_transferFrame hFr hE1 hR1 hA1 hG1
  have hXf : replyTransferCaps st tid c true (arm.pop (arm.leg st c tid rid msg) c tid) =
      .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    unfold replyTransferCaps
    rw [hReq, hTgt, hP1, hHT]
  have hNoY' : (Y1.mapTcbInPlace c (holdMessage msg)).objects.noResizeDue :=
    (SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoY
  rw [replyRecvOnCore_arm_transfer arm st epId tid c rid msg true core ct rt ep rp hAd (hMsg ▸ hSz)
    hT hRO hS hRp hXf hE2 hR2 hA2 hNoY' hG2]
  dsimp only
  subst hMsg
  simp only [CapTransferSummary.capInfo_empty]
  obtain ⟨hE3, ⟨rt3, hR3, hA3⟩, hG3⟩ := receiveReturnSchedContext_receiveGuard true _ tid hNoY'
    hE2 hR2 hA2 hG2
  obtain ⟨t2, hT2, hB2⟩ := receiveBlock_receiver_blocked _ epId ep tid rt3 (some rid) core hE3 hR3
    hA3 hG3
  have hWY := ipcWordReadsAgree_receiveTransferCaps _ _ _ hNoP hT1
  rw [arm.tail_stagedLong Y1 st c tid rid epId ep.recvTailCode core rf len badge s.capInfo hNoY hNe
    hLen ((arm.ipcBufferReadsAgree_tail Y1 tid rid epId ep.recvTailCode core hNoY).words.trans
      (hWY.trans hAP.words)) ⟨t2, hT2, hB2⟩, ← ReplyRecvArm.tailFast_eq]
  have hK := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => deliverLongReplyRecvCapsFrame i (arm.tailFast Y tid rid epId ep.recvTailCode core) c
      rf len tid badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hK
  rw [hAP.frameCapRequestOf, hAP.capTargetOf, hT1] at hK
  unfold performReplyRecvArmCapsDeliveredLong
  rw [hX]
  exact congrArg (fun Z => (.ok ((), Z) : Except KernelError (Unit × SystemState))) hK.symm

end SeLe4n.Kernel
