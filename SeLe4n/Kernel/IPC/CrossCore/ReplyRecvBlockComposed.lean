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

end SeLe4n.Kernel
