/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallInPlace
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace

/-!
# The call that links no reply, written in place

seL4's `sendIPC`, `EPState_Recv`, `do_call`: a call that meets a waiting
receiver which stashed no reply object, or through a capability with neither
`Grant` nor `GrantReply`, delivers its message as a send does (the receiver's
stash dropped, `reply_unlink`) and leaves its caller `Inactive`
(`setThreadState(thread, ThreadState_Inactive)`), with no reply and no
donation (`endpointCallOnCore_noReply_eq`).  The specification reaches each
write through a step that may refuse; here the send rendezvous's checks
(`sendWakesInPlace`) rule every refusal out before the first write, and the
writes run on a state nothing else holds: the send rendezvous with the receiver
woken holding no message (`storeSendRendezvousReady`), the caller taken off its
core and made `Inactive` (`storeCallNoReplyReady`), then the message's frame
written into the receiver's saved registers (`performCallNoReplyDelivered`).
No message is built and none is held.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- The caller a call that links no reply leaves: `Inactive` (seL4's
`setThreadState(thread, ThreadState_Inactive)`), every other field kept; a
fault sender keeps its `pendingFault`. -/
@[inline] def callerInactiveTcb (t : TCB) : TCB := { t with threadState := .Inactive }

/-- **Whether a call meeting the receiver `rt` links no reply**: the payload may
not link one (`SendPayload.canLinkReply`, the capability's `Grant ||
GrantReply`), or the receiver stashed none.  `callRendezvousLinks` asked of the
receiver's TCB in hand. -/
@[inline] def callLinksNoReply (linkReply : Bool) (rt : TCB) : Bool :=
  !(linkReply && rt.pendingReceiveReplyCode != 0)

theorem callRendezvousLinks_false_of {st : SystemState} {r : SeLe4n.ThreadId} {rt : TCB}
    {payload : SendPayload} (hT : st.getTcb? r = some rt)
    (h : callLinksNoReply payload.canLinkReply rt = true) :
    callRendezvousLinks st r payload = false := by
  unfold callLinksNoReply at h
  unfold callRendezvousLinks
  rw [hT]
  simpa only [Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true] using h

/-- The caller's deschedule on its own core and its `Inactive` write: the last
two writes of a call that links no reply. -/
@[inline] def descheduleInactive (X : SystemState) (caller : SeLe4n.ThreadId) (core : CoreId) :
    SystemState :=
  (removeRunnableOnCore X caller core).updateTcb caller callerInactiveTcb

/-- **The no-reply call's writes, the receiver woken holding no message**: the
send rendezvous's (`storeSendRendezvousReady`), the receiver woken on its home
core, the caller descheduled and `Inactive`. -/
@[noinline] def storeCallNoReplyReady (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (core : CoreId) : SystemState :=
  descheduleInactive (wakeThread (storeSendRendezvousReady st endpointId r nextCode) r core).1
    caller core

theorem storeCallNoReplyReady_noResizeDue (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (core : CoreId)
    (hNo : st.objects.noResizeDue) :
    (storeCallNoReplyReady st endpointId caller r nextCode core).objects.noResizeDue := by
  unfold storeCallNoReplyReady descheduleInactive storeSendRendezvousReady
  exact updateTcb_noResizeDue _ _ _ (removeRunnableOnCore_noResizeDue _ _ _
    (wakeThread_noResizeDue _ _ _ (storeSendRendezvousWith_noResizeDue _ _ _ _ _ hNo)))

/-- The send rendezvous holding its message is the rendezvous woken holding
none, the message written in afterwards. -/
theorem storeSendRendezvous_eq_hold (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (msg : IpcMessage)
    (hNo : st.objects.noResizeDue) :
    storeSendRendezvous st endpointId r next msg =
      (storeSendRendezvousReady st endpointId r (ThreadId.optCode next)).mapTcbInPlace r
        (holdMessage msg) := by
  unfold storeSendRendezvousReady
  rw [SeLe4n.ThreadId.ofOptCode_optCode, storeSendRendezvous_eq_with,
    show receiveCompleteTcb msg = holdMessage msg ∘ receiveReadyTcb from rfl,
    storeSendRendezvousWith_comp _ _ _ _ _ _ hNo]

/-- **The no-reply call holds its message in one write**: its writes with the
receiver holding the message are its writes with the receiver holding none,
the message written in afterwards. -/
theorem storeCallNoReply_eq_hold (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (msg : IpcMessage)
    (core : CoreId) (hNo : st.objects.noResizeDue) :
    descheduleInactive (wakeThread (storeSendRendezvous st endpointId r next msg) r core).1
        caller core =
      (storeCallNoReplyReady st endpointId caller r (ThreadId.optCode next) core).mapTcbInPlace r
        (holdMessage msg) := by
  have hNo0 : (storeSendRendezvousReady st endpointId r (ThreadId.optCode next)).objects.noResizeDue :=
    storeSendRendezvousWith_noResizeDue st endpointId r
      (ThreadId.ofOptCode (ThreadId.optCode next)) receiveReadyTcb hNo
  have hNo1 := wakeThread_noResizeDue _ r core hNo0
  have hNo2 := removeRunnableOnCore_noResizeDue _ caller core hNo1
  unfold storeCallNoReplyReady descheduleInactive
  rw [storeSendRendezvous_eq_hold _ _ _ _ _ hNo, wakeThread_msg _ _ _ _ _ _ _ hNo0]
  dsimp only
  rw [removeRunnableOnCore_msg, updateTcb_msg r id (fun _ => some msg) id _ caller callerInactiveTcb hNo2
    (fun _ _ => rfl)]

/-- **The call that links no reply, in place**: under the send rendezvous's
checks (`sendWakesInPlace`) the specification's call that links no reply
(`endpointCallOnCore_noReply_eq`) is the in-place send rendezvous, the
receiver's wake and the caller's `Inactive` deschedule. -/
theorem callNoReply_inPlace (st : SystemState) (endpointId : SeLe4n.ObjId) (ep : Endpoint)
    (caller r : SeLe4n.ThreadId) (rt : TCB) (payload : SendPayload) (msg : IpcMessage)
    (core : CoreId)
    (hM : sendPayloadMessage st caller payload = msg)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.receiveQ.head = some r)
    (hT : st.objects[r.toObjId]? = some (.tcb rt))
    (hLinks : callRendezvousLinks st r payload = false)
    (hG : sendWakesInPlace st endpointId r rt.queueNext = true) :
    endpointCallOnCore endpointId caller payload core st =
      (descheduleInactive (wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r
          core).1 caller core,
       .ok (wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r core).2) := by
  subst hM
  have h := sendRendezvous_inPlace_eq st endpointId ep r rt
    (sendPayloadMessage st caller payload) hE hH hT hG
  rcases hPop : endpointQueuePopHead endpointId true st with e | ⟨r', t0, st'⟩
  · rw [hPop] at h; cases h
  · rw [hPop] at h
    dsimp only at h
    rcases hSt : storeTcbReceiveComplete st' r' (some (sendPayloadMessage st caller payload)) with e | st''
    · rw [hSt] at h; cases h
    · rw [hSt] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact endpointCallOnCore_noReply_eq endpointId caller payload core st ep r' t0 st' _ hE hH
        hLinks hPop hSt

/-- **The call dispatch that links no reply, in place**: with no capability to
transfer, the dispatch is the in-place no-reply call with an empty transfer
summary -- no donation and no priority walk, as seL4's `sendIPC` lends nothing
to a call that pushes no reply. -/
theorem callDispatch_noReply_inPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (caller r : SeLe4n.ThreadId) (rt : TCB) (payload : SendPayload)
    (msg : IpcMessage) (core : CoreId)
    (hM : sendPayloadMessage st caller payload = msg)
    (hReq : sendCapRequest st endpointId caller payload = none)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.receiveQ.head = some r)
    (hT : st.objects[r.toObjId]? = some (.tcb rt))
    (hLinks : callRendezvousLinks st r payload = false)
    (hG : sendWakesInPlace st endpointId r rt.queueNext = true) :
    endpointCallCrossCoreDispatch endpointId caller payload core st =
      (descheduleInactive (wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r
          core).1 caller core,
       .ok ({ results := #[] },
         (wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r core).2)) := by
  have hEp : st.getEndpoint? endpointId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE
  unfold endpointCallCrossCoreDispatch
  rw [endpointCallWithCapsOnCore_no_caps _ _ _ _ _ hReq,
    callNoReply_inPlace st endpointId ep caller r rt payload msg core hM hE hH hT hLinks hG]
  simp only [hEp, hH, hLinks, Except.map, Bool.false_eq_true, ↓reduceIte]

/-- The checked form: under the flow gate, the in-place no-reply call. -/
theorem callDispatchChecked_noReply_inPlace (ctx : LabelingContext) (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (caller r : SeLe4n.ThreadId) (rt : TCB)
    (payload : SendPayload) (msg : IpcMessage) (core : CoreId)
    (hM : sendPayloadMessage st caller payload = msg)
    (hReq : sendCapRequest st endpointId caller payload = none)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.receiveQ.head = some r)
    (hT : st.objects[r.toObjId]? = some (.tcb rt))
    (hLinks : callRendezvousLinks st r payload = false)
    (hG : sendWakesInPlace st endpointId r rt.queueNext = true)
    (hFlow : endpointFlowGate ctx endpointId (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) = true) :
    endpointCallCrossCoreDispatchChecked ctx endpointId caller payload core st =
      (descheduleInactive (wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r
          core).1 caller core,
       .ok ({ results := #[] },
         (wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r core).2)) := by
  unfold endpointCallCrossCoreDispatchChecked
  rw [if_pos hFlow]
  exact callDispatch_noReply_inPlace st endpointId ep caller r rt payload msg core hM hReq hE hH
    hT hLinks hG

/-- **The no-reply call, delivered**: the receiver woken holding no message,
the caller descheduled and `Inactive`, then the message's frame written into
the receiver's saved registers.  The message is built only where the receiver
is, unexpectedly, not ready. -/
@[noinline] def performCallNoReplyDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : CoreId) : SystemState :=
  let X := storeCallNoReplyReady st endpointId caller r nextCode core
  writeDeliveredFrameIfReady X r (Architecture.regMessageFrameW layout rf len badgeWord badged)
    (fun _ => holdDeliveredBody X r layout rf len (SeLe4n.Badge.opt badgeWord badged))

/-- **The staged no-reply call is the delivered one** for a message of at most
four words read in the caller's registers. -/
theorem stageWokenDelivery_callNoReply (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : CoreId)
    (hNo : st.objects.noResizeDue) (hSz : Architecture.regMessageLength layout len ≤ 4) :
    Architecture.stageWokenDelivery
        (descheduleInactive (wakeThread (storeSendRendezvous st endpointId r next
          { registers := Architecture.regMessageBody layout rf len,
            badge := SeLe4n.Badge.opt badgeWord badged }) r core).1 caller core)
        (some r) 0 =
      performCallNoReplyDelivered st endpointId caller r (ThreadId.optCode next) layout rf len
        badgeWord badged core := by
  have hNoS := storeCallNoReplyReady_noResizeDue st endpointId caller r (ThreadId.optCode next)
    core hNo
  unfold performCallNoReplyDelivered
  rw [Architecture.regMessageFrameW_eq, storeCallNoReply_eq_hold _ _ _ _ _ _ _ hNo,
    Architecture.stageWokenDelivery_some,
    stageDeliveredMessage_holdMessage _ _ _ hNoS
      (by rw [Architecture.regMessageBody_size]; exact hSz),
    Architecture.returnFrameOfMessage_regMessageBody]
  rfl

end SeLe4n.Kernel
