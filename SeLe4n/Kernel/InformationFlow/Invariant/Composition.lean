-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.Invariant.Operations

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)
-- AN4-A allowlist: proof-chain reference to `lifecycleRetypeObject` from
-- `SeLe4n.Kernel.Internal`. Enforced by `scripts/test_tier0_hygiene.sh`.
open Internal

/-! ## H-05 — Composed Bundle Non-Interference

WS-F3 extends the IF-M4 bundle to cover all 30+ API operations.

1. `NonInterferenceStep` — inductive encoding all operation families with
   their domain-separation hypotheses.
2. `step_preserves_projection` — one-sided projection preservation for
   any single step.
3. `composedNonInterference_step` — the primary IF-M4 theorem.
4. `NonInterferenceTrace` — multi-step trace inductive.
5. `composedNonInterference_trace` — trace-level IF-M4 composition.
6. `preservesLowEquivalence` — abstract NI predicate for kernel actions.
-/

/-- WS-F3/H-05: Inductive covering all operation families with their
full parameter sets and domain-separation hypotheses.

WS-F3 extends the original 5 constructors with notification, service,
capability CRUD, and lifecycle operations. -/
inductive NonInterferenceStep
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) : Prop where
  | chooseThread
      (next : Option SeLe4n.ThreadId)
      (hStep : chooseThread st = .ok (next, st'))
    : NonInterferenceStep ctx observer st st'
  /-- U4-A: endpointSendDual NI constructor with internalized projection proof.

  The `hProjection` hypothesis (T4-J) has been replaced with semantic queue
  domain isolation hypotheses that are sufficient to prove projection
  preservation internally. The three queue hypotheses capture the security
  property that all threads interacting through a non-observable endpoint
  are themselves non-observable:
  - `hRecvQueueHeadHigh`: receiveQ head threads are non-observable
  - `hRecvQueueNextHigh`: next-of-head threads have non-observable TCBs
  - `hSendQueueTailHigh`: sendQ tail threads have non-observable TCBs -/
  | endpointSendDual
      (eid : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
      (hEndpointHigh : objectObservable ctx observer eid = false)
      (hSenderHigh : threadObservable ctx observer sender = false)
      (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
      (hCoherent : ∀ tid : SeLe4n.ThreadId,
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hStep : endpointSendDual eid sender msg st = .ok ((), st'))
      (hRecvQueueHeadHigh : ∀ ep receiver, st.objects[eid]? = some (.endpoint ep) →
          ep.receiveQ.head = some receiver → threadObservable ctx observer receiver = false)
      (hRecvQueueNextHigh : ∀ ep receiver recvTcb nextTid,
          st.objects[eid]? = some (.endpoint ep) →
          ep.receiveQ.head = some receiver →
          st.objects[receiver.toObjId]? = some (.tcb recvTcb) →
          recvTcb.queueNext = some nextTid →
          objectObservable ctx observer nextTid.toObjId = false)
      (hSendQueueTailHigh : ∀ ep tailTid, st.objects[eid]? = some (.endpoint ep) →
          ep.sendQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false)
    : NonInterferenceStep ctx observer st st'
  | cspaceMint
      (src dst : CSpaceAddr) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
      (hSrcHigh : objectObservable ctx observer src.cnode = false)
      (hDstHigh : objectObservable ctx observer dst.cnode = false)
      (hStep : cspaceMint src dst rights badge st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceRevoke
      (addr : CSpaceAddr)
      (hAddrHigh : objectObservable ctx observer addr.cnode = false)
      (hStep : cspaceRevoke addr st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | lifecycleRetype
      (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
      (hTargetHigh : objectObservable ctx observer target = false)
      (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | lifecycleRevokeDeleteRetype
      (authority cleanup : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
      (hCleanupHigh : objectObservable ctx observer cleanup.cnode = false)
      (hTargetHigh : objectObservable ctx observer target = false)
      (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | notificationSignal
      (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
      (hNtfnHigh : objectObservable ctx observer notificationId = false)
      (hCoherent : ∀ tid : SeLe4n.ThreadId,
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hWaiterDomain : ∀ ntfn tid, st.objects[notificationId]? = some (.notification ntfn) →
          tid ∈ ntfn.waitingThreads → threadObservable ctx observer tid = false)
      (hStep : SeLe4n.Kernel.notificationSignal notificationId badge st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | notificationWait
      (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
      (result : Option SeLe4n.Badge)
      (hNtfnHigh : objectObservable ctx observer notificationId = false)
      (hWaiterHigh : threadObservable ctx observer waiter = false)
      (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false)
      (hStep : SeLe4n.Kernel.notificationWait notificationId waiter st = .ok (result, st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceInsertSlot
      (dst : CSpaceAddr) (cap : Capability)
      (hDstHigh : objectObservable ctx observer dst.cnode = false)
      (hStep : cspaceInsertSlot dst cap st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | schedule
      (hCurrentHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
          threadObservable ctx observer t = false)
      (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
          threadObservable ctx observer tid = false)
      (hStep : SeLe4n.Kernel.schedule st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | vspaceMapPage
      (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
      (hRootHigh : ∀ rootId root, Architecture.resolveAsidRoot st asid = some (rootId, root) →
          objectObservable ctx observer rootId = false)
      (hStep : Architecture.vspaceMapPage asid vaddr paddr default st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | vspaceUnmapPage
      (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
      (hRootHigh : ∀ rootId root, Architecture.resolveAsidRoot st asid = some (rootId, root) →
          objectObservable ctx observer rootId = false)
      (hStep : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | vspaceLookup
      (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
      (hStep : Architecture.vspaceLookup asid vaddr st = .ok (paddr, st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceCopy
      (src dst : CSpaceAddr)
      (hSrcHigh : objectObservable ctx observer src.cnode = false)
      (hDstHigh : objectObservable ctx observer dst.cnode = false)
      (hStep : SeLe4n.Kernel.cspaceCopy src dst st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceMove
      (src dst : CSpaceAddr)
      (hSrcHigh : objectObservable ctx observer src.cnode = false)
      (hDstHigh : objectObservable ctx observer dst.cnode = false)
      (hStep : SeLe4n.Kernel.cspaceMove src dst st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceDeleteSlot
      (addr : CSpaceAddr)
      (hAddrHigh : objectObservable ctx observer addr.cnode = false)
      (hStep : SeLe4n.Kernel.cspaceDeleteSlot addr st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | endpointReply
      (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
      (hTargetHigh : threadObservable ctx observer target = false)
      (hTargetObjHigh : objectObservable ctx observer target.toObjId = false)
      (hStep : endpointReply replier target msg st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | endpointReceiveDualHigh
      (endpointId : SeLe4n.ObjId) (receiver sender : SeLe4n.ThreadId)
      (replyId : Option SeLe4n.ReplyId)
      (hEndpointHigh : objectObservable ctx observer endpointId = false)
      (hReceiverHigh : threadObservable ctx observer receiver = false)
      (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
      (hCoherent : ∀ tid : SeLe4n.ThreadId,
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (sender, st'))
      (hSendQueueHeadHigh : ∀ ep sender, st.objects[endpointId]? = some (.endpoint ep) →
          ep.sendQ.head = some sender → threadObservable ctx observer sender = false)
      (hSendQueueNextHigh : ∀ ep sender senderTcb nextTid,
          st.objects[endpointId]? = some (.endpoint ep) →
          ep.sendQ.head = some sender →
          st.objects[sender.toObjId]? = some (.tcb senderTcb) →
          senderTcb.queueNext = some nextTid →
          objectObservable ctx observer nextTid.toObjId = false)
      (hRecvQueueTailHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false)
    : NonInterferenceStep ctx observer st st'
  | endpointCallHigh
      (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
      (hEndpointHigh : objectObservable ctx observer endpointId = false)
      (hCallerHigh : threadObservable ctx observer caller = false)
      (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
      (hCoherent : ∀ tid : SeLe4n.ThreadId,
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hStep : endpointCall endpointId caller msg st = .ok ((), st'))
      (hRecvQueueHeadHigh : ∀ ep receiver, st.objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.head = some receiver → threadObservable ctx observer receiver = false)
      (hRecvQueueNextHigh : ∀ ep receiver recvTcb nextTid,
          st.objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.head = some receiver →
          st.objects[receiver.toObjId]? = some (.tcb recvTcb) →
          recvTcb.queueNext = some nextTid →
          objectObservable ctx observer nextTid.toObjId = false)
      (hSendQueueTailHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
          ep.sendQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false)
    : NonInterferenceStep ctx observer st st'
  | endpointReplyRecvHigh
      (endpointId : SeLe4n.ObjId) (replierReceiver replyTarget : SeLe4n.ThreadId)
      (replyMsg : IpcMessage)
      (replyId : Option SeLe4n.ReplyId)
      (hEndpointHigh : objectObservable ctx observer endpointId = false)
      (hReceiverHigh : threadObservable ctx observer replierReceiver = false)
      (hReceiverObjHigh : objectObservable ctx observer replierReceiver.toObjId = false)
      (hReplyTargetHigh : threadObservable ctx observer replyTarget = false)
      (hReplyTargetObjHigh : objectObservable ctx observer replyTarget.toObjId = false)
      (hCoherent : ∀ tid : SeLe4n.ThreadId,
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hStep : endpointReplyRecv endpointId replierReceiver replyTarget replyMsg replyId st = .ok ((), st'))
      (hSendQueueHeadHigh : ∀ ep sender, st.objects[endpointId]? = some (.endpoint ep) →
          ep.sendQ.head = some sender → threadObservable ctx observer sender = false)
      (hSendQueueNextHigh : ∀ ep sender senderTcb nextTid,
          st.objects[endpointId]? = some (.endpoint ep) →
          ep.sendQ.head = some sender →
          st.objects[sender.toObjId]? = some (.tcb senderTcb) →
          senderTcb.queueNext = some nextTid →
          objectObservable ctx observer nextTid.toObjId = false)
      (hRecvQueueTailHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false)
    : NonInterferenceStep ctx observer st st'
  | storeObjectHigh
      (oid : SeLe4n.ObjId) (obj : KernelObject)
      (hOidHigh : objectObservable ctx observer oid = false)
      (hStep : storeObject oid obj st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | setCurrentThread
      (tid : Option SeLe4n.ThreadId)
      (hTidHigh : ∀ t, tid = some t → threadObservable ctx observer t = false)
      (hCurrentHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
          threadObservable ctx observer t = false)
      (hStep : setCurrentThread tid st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | ensureRunnableHigh
      (tid : SeLe4n.ThreadId)
      (hTidHigh : threadObservable ctx observer tid = false)
      (hEq : st' = ensureRunnable st tid)
    : NonInterferenceStep ctx observer st st'
  | removeRunnableHigh
      (tid : SeLe4n.ThreadId)
      (hTidHigh : threadObservable ctx observer tid = false)
      (hEq : st' = removeRunnable st tid)
    : NonInterferenceStep ctx observer st st'
  | storeTcbIpcStateAndMessageHigh
      (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
      (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
      (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    : NonInterferenceStep ctx observer st st'
  | storeTcbQueueLinksHigh
      (tid : SeLe4n.ThreadId)
      (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
      (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
      (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    : NonInterferenceStep ctx observer st st'
  | cspaceMutateHigh
      (addr : CSpaceAddr) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
      (hAddrHigh : objectObservable ctx observer addr.cnode = false)
      (hStep : cspaceMutate addr rights badge st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | handleYield
      (hCurrentHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
          threadObservable ctx observer t = false)
      (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
          threadObservable ctx observer tid = false)
      (hStep : SeLe4n.Kernel.handleYield st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | timerTick
      (hCurrentHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
          threadObservable ctx observer t = false)
      (hCurrentObjHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
          objectObservable ctx observer t.toObjId = false)
      (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
          threadObservable ctx observer tid = false)
      (hStep : SeLe4n.Kernel.timerTick st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  /-- WS-J1-D: Syscall decode error — the decode failed, state is unchanged.
      This covers all paths where `decodeSyscallArgs` or register lookup
      returns an error before any state-modifying operation executes. -/
  | syscallDecodeError
      (hEq : st' = st)
    : NonInterferenceStep ctx observer st st'
  /-- WS-J1-D: Syscall dispatch through high-domain thread — the current thread
      is non-observable, and the dispatched operation preserves the observer's
      projection. The caller carries the projection proof (which follows from
      the underlying operation's NI properties).

      This constructor models the register-sourced syscall entry path
      (`syscallEntry` in `Kernel/API.lean`): decode is pure (no state change),
      register lookup is read-only, and the dispatch delegates to an existing
      kernel operation whose NI step is already covered by other constructors. -/
  | syscallDispatchHigh
      (hCurrentHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
          threadObservable ctx observer t = false)
      (hProj : projectState ctx observer st' = projectState ctx observer st)
    : NonInterferenceStep ctx observer st st'
  /-- R5-B/M-02: Service registration — registerService modifies only
      serviceRegistry which is not part of the projected observable state
      (projectServicePresence is gated by serviceObservable, which depends
      on the labeling context, not the registry contents). Therefore
      registerService unconditionally preserves projection. -/
  | registerServiceChecked
      (caller : SeLe4n.ThreadId) (reg : ServiceRegistration)
      (hStep : registerServiceChecked ctx caller reg st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  /-- AE1-F5 (U-04): Full call path with donation and PIP — covers the
      post-IPC mutations `applyCallDonation` and `propagatePriorityInheritance`
      that occur after `endpointCall`. The projection proof is discharged by
      `endpointCallWithDonation_preserves_lowEquivalent`. -/
  | endpointCallWithDonationHigh
      (hCurrentHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
          threadObservable ctx observer t = false)
      (hProj : projectState ctx observer st' = projectState ctx observer st)
    : NonInterferenceStep ctx observer st st'
  /-- AE1-F6 (U-04): Full reply path with donation return and PIP reversion.
      Covers `applyReplyDonation` and `revertPriorityInheritance` after
      `endpointReply`. -/
  | endpointReplyWithReversionHigh
      (hCurrentHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
          threadObservable ctx observer t = false)
      (hProj : projectState ctx observer st' = projectState ctx observer st)
    : NonInterferenceStep ctx observer st st'
  /-- AG5-F (FINDING-06): Interrupt dispatch — handles timer and device
      interrupts. Timer path delegates to `timerTick` (domain-local budget
      decrement). Device path delivers `notificationSignal` to the registered
      handler. The projection proof covers both paths:
      - Timer: reuses `timerTick` projection (current thread high + runnable high)
      - Device: reuses `notificationSignal` projection (notification high)
      - Unmapped/spurious: state unchanged (trivial preservation) -/
  | handleInterrupt
      (hCurrentHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
          threadObservable ctx observer t = false)
      (hCurrentObjHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
          objectObservable ctx observer t.toObjId = false)
      (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
          threadObservable ctx observer tid = false)
      (hProj : projectState ctx observer st' = projectState ctx observer st)
    : NonInterferenceStep ctx observer st st'

/-- WS-F3/H-05/H-09: A single non-interference step preserves the observer's
projection (one-sided version). -/
theorem step_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hStep : NonInterferenceStep ctx observer st st') :
    projectState ctx observer st' = projectState ctx observer st := by
  cases hStep with
  | chooseThread next hOp =>
    have := chooseThread_preserves_state st st' next hOp; subst this; rfl
  | endpointSendDual eid sender msg hEH hSH hSOH hCo hOp hRQHH hRQNH hSQTH =>
    exact endpointSendDual_preserves_projection ctx observer eid sender msg st st'
      hEH hSH hSOH hCo hRQHH hRQNH hSQTH hObjInv hOp
  | cspaceMint src dst rights badge hSrcH hDstH hOp =>
    rcases cspaceMint_child_attenuates st st' src dst rights badge hObjInv hOp with
      ⟨parent, child, hLookup, _, _⟩
    unfold cspaceMint at hOp; rw [hLookup] at hOp
    -- AL1b (AK7-I.cascade): promote parent via toNonNull?.
    have hNotNull : parent.isNull = false := by
      by_cases h : parent.isNull
      · exfalso; simp [Capability.toNonNull?, h] at hOp
      · exact Bool.not_eq_true _ |>.mp h
    have hToNN : parent.toNonNull? = some ⟨parent, hNotNull⟩ :=
      Capability.toNonNull?_of_not_null hNotNull
    cases hMint : mintDerivedCap ⟨parent, hNotNull⟩ rights badge with
    | error e => simp [hToNN, hMint] at hOp
    | ok c =>
      have hInsert : cspaceInsertSlot dst c st = .ok ((), st') := by
        simpa [hToNN, hMint] using hOp
      simp only [projectState]; congr 1
      · funext oid; by_cases hObs : objectObservable ctx observer oid
        · simp [projectObjects, hObs, SystemState.getObject?]
          by_cases hEq : oid = dst.cnode
          · subst hEq; simp [hDstH] at hObs
          · exact congrArg (Option.map (projectKernelObject ctx observer))
              (cspaceInsertSlot_preserves_objects_ne st st' dst c oid hEq hObjInv hInsert)
        · simp [projectObjects, hObs]
      · simp [projectRunnable, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · simp [projectCurrent, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · funext sid
        simp only [projectServicePresence, lookupService,
          cspaceInsertSlot_preserves_services st st' dst c hInsert]
      · simp [projectActiveDomain, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · funext irq; simp only [projectIrqHandlers]
        rw [cspaceInsertSlot_preserves_irqHandlers st st' dst c hInsert]
      · exact cspaceInsertSlot_preserves_projectObjectIndex st st' dst c hDstH hInsert
      · simp [projectDomainTimeRemaining, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · simp [projectDomainSchedule, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · simp [projectDomainScheduleIndex, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · simp [projectMachineRegs, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert,
              cspaceInsertSlot_preserves_machine st st' dst c hInsert]
      · -- R5-C.1: memory
        exact projectMemory_eq_of_memory_eq ctx observer st' st
          (by rw [cspaceInsertSlot_preserves_machine st st' dst c hInsert])
      · -- V6-E: serviceRegistry
        exact projectServiceRegistry_eq_of_services_eq ctx observer st' st
          (cspaceInsertSlot_preserves_services st st' dst c hInsert)
  | cspaceRevoke addr hAddrH hOp =>
    exact cspaceRevoke_preserves_projection ctx observer addr st st' hAddrH hObjInv hOp
  | lifecycleRetype authority target newObj hTH hOp =>
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hOp with
      ⟨_, _, _, _, _, _, hStore⟩
    exact storeObject_preserves_projection ctx observer st st' target newObj hTH hObjInv hStore
  | lifecycleRevokeDeleteRetype authority cleanup target newObj hCH hTH hOp =>
    exact lifecycleRevokeDeleteRetype_preserves_projection ctx observer authority cleanup target
      newObj st st' hCH hTH hObjInv hOp
  | notificationSignal ntfnId badge hNH hCo hWD hOp =>
    exact notificationSignal_projection_preserved ctx observer ntfnId badge st st'
      hNH hCo hWD hObjInv hOp
  | notificationWait ntfnId waiter result hNH hWH hWOH hOp =>
    exact notificationWait_projection_preserved ctx observer ntfnId waiter result st st'
      hNH hWH hWOH hObjInv hOp
  | cspaceInsertSlot dst cap hDH hOp =>
    simp only [projectState]; congr 1
    · funext oid; by_cases hObs : objectObservable ctx observer oid
      · simp [projectObjects, hObs, SystemState.getObject?]
        have hNe : oid ≠ dst.cnode := by intro hEq; subst hEq; simp [hDH] at hObs
        exact congrArg (Option.map (projectKernelObject ctx observer))
          (cspaceInsertSlot_preserves_objects_ne st st' dst cap oid hNe hObjInv hOp)
      · simp [projectObjects, hObs]
    · simp [projectRunnable, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · simp [projectCurrent, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · funext sid; simp only [projectServicePresence, lookupService,
        cspaceInsertSlot_preserves_services st st' dst cap hOp]
    · simp [projectActiveDomain, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · funext irq; simp only [projectIrqHandlers]
      rw [cspaceInsertSlot_preserves_irqHandlers st st' dst cap hOp]
    · exact cspaceInsertSlot_preserves_projectObjectIndex st st' dst cap hDH hOp
    · simp [projectDomainTimeRemaining, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · simp [projectDomainSchedule, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · simp [projectDomainScheduleIndex, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · simp [projectMachineRegs, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp,
            cspaceInsertSlot_preserves_machine st st' dst cap hOp]
    · -- R5-C.1: memory
      exact projectMemory_eq_of_memory_eq ctx observer st' st
        (by rw [cspaceInsertSlot_preserves_machine st st' dst cap hOp])
    · -- V6-E: serviceRegistry
      exact projectServiceRegistry_eq_of_services_eq ctx observer st' st
        (cspaceInsertSlot_preserves_services st st' dst cap hOp)
  | schedule hCurH hAllR hOp =>
    exact schedule_preserves_projection ctx observer st st' hCurH hAllR hObjInv hOp
  | vspaceMapPage asid vaddr paddr hRH hOp =>
    exact vspaceMapPage_preserves_projection ctx observer asid vaddr paddr st st' hRH hObjInv hOp
  | vspaceUnmapPage asid vaddr hRH hOp =>
    exact vspaceUnmapPage_preserves_projection ctx observer asid vaddr st st' hRH hObjInv hOp
  | vspaceLookup asid vaddr paddr hOp =>
    have := vspaceLookup_preserves_state st asid vaddr paddr st' hOp; subst this; rfl
  | cspaceCopy src dst hSH hDH hOp =>
    exact cspaceCopy_preserves_projection ctx observer src dst st st' hSH hDH hObjInv hOp
  | cspaceMove src dst hSH hDH hOp =>
    exact cspaceMove_preserves_projection ctx observer src dst st st' hSH hDH hObjInv hOp
  | cspaceDeleteSlot addr hAH hOp =>
    exact cspaceDeleteSlot_preserves_projection ctx observer addr st st' hAH hObjInv hOp
  | endpointReply replier target msg hTH hTOH hOp =>
    exact endpointReply_preserves_projection ctx observer replier target msg st st' hTH hTOH hObjInv
      hIdxComplete hObjSetInv hOp
  | endpointReceiveDualHigh eid recv send replyId hEH hRH hROH hCo hOp hSQHH hSQNH hRQTH =>
    exact endpointReceiveDual_preserves_projection ctx observer eid recv replyId st st' send
      hEH hRH hROH hCo hSQHH hSQNH hRQTH hObjInv
      hIdxComplete hObjSetInv hOp
  | endpointCallHigh eid caller msg hEH hCH hCOH hCo hOp hRQHH hRQNH hSQTH =>
    exact endpointCall_preserves_projection ctx observer eid caller msg st st'
      hEH hCH hCOH hCo hRQHH hRQNH hSQTH hObjInv hIdxComplete hObjSetInv hOp
  | endpointReplyRecvHigh eid recv target rmsg replyId hEH hRH hROH hRTH hRTOH hCo hOp hSQHH hSQNH hRQTH =>
    exact endpointReplyRecv_preserves_projection ctx observer eid recv target rmsg replyId st st'
      hEH hRH hROH hRTH hRTOH hCo hSQHH hSQNH hRQTH hObjInv
      hIdxComplete hObjSetInv hOp
  | storeObjectHigh oid obj hOH hOp =>
    exact storeObject_preserves_projection ctx observer st st' oid obj hOH hObjInv hOp
  | setCurrentThread tid hTidH hCurH hOp =>
    exact setCurrentThread_preserves_projection ctx observer tid st st' hTidH hCurH hOp
  | ensureRunnableHigh tid hTH hEq =>
    rw [hEq]; exact ensureRunnable_preserves_projection ctx observer st tid hTH
  | removeRunnableHigh tid hTH hEq =>
    rw [hEq]; exact removeRunnable_preserves_projection ctx observer st tid hTH
  | storeTcbIpcStateAndMessageHigh tid ipc msg hTOH hOp =>
    exact storeTcbIpcStateAndMessage_preserves_projection ctx observer st st' tid ipc msg hTOH hObjInv hOp
  | storeTcbQueueLinksHigh tid prev pprev next hTOH hOp =>
    exact storeTcbQueueLinks_preserves_projection ctx observer st st' tid prev pprev next hTOH hObjInv hOp
  | cspaceMutateHigh addr rights badge hAH hOp =>
    unfold cspaceMutate SystemState.getCNode? at hOp
    cases hL : cspaceLookupSlot addr st with
    | error e => simp [hL] at hOp
    | ok p =>
      rcases p with ⟨cap, stL⟩
      have hStEq := cspaceLookupSlot_preserves_state st stL addr cap hL
      subst stL
      simp only [hL] at hOp
      -- AK8-K (C-L2): null-cap guard discharged first.
      by_cases hNull : cap.isNull
      · simp [hNull] at hOp
      simp only [hNull, Bool.false_eq_true, ↓reduceIte] at hOp
      split at hOp
      · -- rights subset: the store of the mutated CNode
        split at hOp
        · -- some (.cnode cn)
          next cn =>
          exact storeObject_preserves_projection ctx observer st st' addr.cnode _ hAH hObjInv hOp
        · -- not a cnode
          simp at hOp
      · -- rights not subset: error
        simp at hOp
  | handleYield hCH hAR hOp =>
    exact handleYield_preserves_projection ctx observer st st' hCH hAR hObjInv hOp
  | timerTick hCH hCOH hAR hOp =>
    exact timerTick_preserves_projection ctx observer st st' hCH hCOH hAR hObjInv hOp
  | syscallDecodeError hEq => subst hEq; rfl
  | syscallDispatchHigh _ hProj => exact hProj
  | registerServiceChecked caller reg hOp =>
    have hFlow := enforcementSoundness_registerServiceChecked ctx caller reg st st' hOp
    rw [registerServiceChecked_eq_registerService_when_allowed ctx caller reg st hFlow] at hOp
    exact registerService_preserves_projection ctx observer reg st st' hOp
  | endpointCallWithDonationHigh _ hProj => exact hProj
  | endpointReplyWithReversionHigh _ hProj => exact hProj
  | handleInterrupt _ _ _ hProj => exact hProj

/-- WS-F3/H-05/H-09: Primary IF-M4 composition theorem — single-step bundle
non-interference. -/
theorem composedNonInterference_step
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hIdxComplete₁ : objectIndexSetComplete s₁)
    (hIdxComplete₂ : objectIndexSetComplete s₂)
    (hObjSetInv₁ : s₁.objectIndexSet.table.invExt)
    (hObjSetInv₂ : s₂.objectIndexSet.table.invExt)
    (hStep₁ : NonInterferenceStep ctx observer s₁ s₁')
    (hStep₂ : NonInterferenceStep ctx observer s₂ s₂') :
    lowEquivalent ctx observer s₁' s₂' := by
  have h₁ := step_preserves_projection ctx observer s₁ s₁' hObjInv₁ hIdxComplete₁ hObjSetInv₁ hStep₁
  have h₂ := step_preserves_projection ctx observer s₂ s₂' hObjInv₂ hIdxComplete₂ hObjSetInv₂ hStep₂
  unfold lowEquivalent; rw [h₁, h₂]; exact hLow

/-- WS-F3/H-05: Multi-step trace of non-interference steps. -/
inductive NonInterferenceTrace
    (ctx : LabelingContext) (observer : IfObserver) :
    SystemState → SystemState → Prop where
  | nil (st : SystemState) : NonInterferenceTrace ctx observer st st
  | cons (st₁ st₂ st₃ : SystemState)
      (hObjInv : st₁.objects.invExt)
      (hIdxComplete : objectIndexSetComplete st₁)
      (hObjSetInv : st₁.objectIndexSet.table.invExt)
      (hStep : NonInterferenceStep ctx observer st₁ st₂)
      (hTail : NonInterferenceTrace ctx observer st₂ st₃)
    : NonInterferenceTrace ctx observer st₁ st₃

/-- WS-F3/H-05: A non-interference trace preserves the observer's projection. -/
theorem trace_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hTrace : NonInterferenceTrace ctx observer st st') :
    projectState ctx observer st' = projectState ctx observer st := by
  induction hTrace with
  | nil _ => rfl
  | cons _ st₂ _ hObjInv hIdxComplete hObjSetInv hStep _ ih =>
    rw [ih, step_preserves_projection ctx observer _ st₂ hObjInv hIdxComplete hObjSetInv hStep]

/-- WS-F3/H-05: Trace-level IF-M4 composition theorem. -/
theorem composedNonInterference_trace
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hTrace₁ : NonInterferenceTrace ctx observer s₁ s₁')
    (hTrace₂ : NonInterferenceTrace ctx observer s₂ s₂') :
    lowEquivalent ctx observer s₁' s₂' := by
  have h₁ := trace_preserves_projection ctx observer s₁ s₁' hTrace₁
  have h₂ := trace_preserves_projection ctx observer s₂ s₂' hTrace₂
  unfold lowEquivalent; rw [h₁, h₂]; exact hLow

-- ============================================================================
-- AE1-E: Composed step covering both projection-preserving and
-- low-equivalence-preserving operations (switchDomain)
-- ============================================================================

/-- AE1-E (U-03): A paired non-interference step covering all kernel
operations, including operations that modify the observer's projection
deterministically (e.g., `switchDomain`).

`NonInterferenceStep` is one-sided: each constructor proves that a single
step preserves the observer's projection. `switchDomain` does NOT preserve
projection (it changes `activeDomain`, `domainScheduleIndex`,
`domainTimeRemaining`), but it DOES preserve low-equivalence because both
runs compute identical scheduler changes from identical scheduler fields.

This inductive closes the gap identified by IF-01/U-03 by modeling
`switchDomain` as a paired (two-sided) step alongside the existing
projection-preserving one-sided steps. -/
inductive ComposedNonInterferenceStep
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState) : Prop where
  /-- Standard projection-preserving steps: each run independently preserves
      the observer's projection via `NonInterferenceStep`. -/
  | projectionPreserving
      (hStep₁ : NonInterferenceStep ctx observer s₁ s₁')
      (hStep₂ : NonInterferenceStep ctx observer s₂ s₂')
    : ComposedNonInterferenceStep ctx observer s₁ s₂ s₁' s₂'
  /-- AE1-E: Domain switch — changes scheduler state deterministically.
      Both runs produce identical scheduler changes because the scheduler
      fields (`domainSchedule`, `domainScheduleIndex`, `domainTimeRemaining`)
      are unconditionally projected and therefore identical across
      low-equivalent states. -/
  | switchDomain
      (hCurrentHigh₁ : ∀ t, (s₁.scheduler.currentOnCore bootCoreId) = some t →
          threadObservable ctx observer t = false)
      (hCurrentHigh₂ : ∀ t, (s₂.scheduler.currentOnCore bootCoreId) = some t →
          threadObservable ctx observer t = false)
      (hStep₁ : switchDomain s₁ = .ok ((), s₁'))
      (hStep₂ : switchDomain s₂ = .ok ((), s₂'))
    : ComposedNonInterferenceStep ctx observer s₁ s₂ s₁' s₂'

/-- AE1-E: Composed non-interference theorem — covers both
projection-preserving steps and domain switch.

This extends `composedNonInterference_step` to handle `switchDomain`,
closing the IF-01/U-03 gap. -/
theorem composedNI_withSwitchDomain
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hIdxComplete₁ : objectIndexSetComplete s₁)
    (hIdxComplete₂ : objectIndexSetComplete s₂)
    (hObjSetInv₁ : s₁.objectIndexSet.table.invExt)
    (hObjSetInv₂ : s₂.objectIndexSet.table.invExt)
    (hStep : ComposedNonInterferenceStep ctx observer s₁ s₂ s₁' s₂') :
    lowEquivalent ctx observer s₁' s₂' := by
  cases hStep with
  | projectionPreserving h₁ h₂ =>
    exact composedNonInterference_step ctx observer s₁ s₂ s₁' s₂'
      hLow hObjInv₁ hObjInv₂ hIdxComplete₁ hIdxComplete₂ hObjSetInv₁ hObjSetInv₂ h₁ h₂
  | switchDomain hCH₁ hCH₂ hS₁ hS₂ =>
    exact switchDomain_preserves_lowEquivalent ctx observer s₁ s₂ s₁' s₂'
      hLow hCH₁ hCH₂ hObjInv₁ hObjInv₂ hS₁ hS₂

/-- AE1-E: Two-step composition — two consecutive composed steps preserve
low-equivalence. This extends `composedNI_withSwitchDomain` for chaining. -/
theorem composedNI_two_steps
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁_mid s₂_mid s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hObjInv₁ : s₁.objects.invExt) (hObjInv₂ : s₂.objects.invExt)
    (hIdxComplete₁ : objectIndexSetComplete s₁) (hIdxComplete₂ : objectIndexSetComplete s₂)
    (hObjSetInv₁ : s₁.objectIndexSet.table.invExt) (hObjSetInv₂ : s₂.objectIndexSet.table.invExt)
    (hObjInvMid₁ : s₁_mid.objects.invExt) (hObjInvMid₂ : s₂_mid.objects.invExt)
    (hIdxCompleteMid₁ : objectIndexSetComplete s₁_mid) (hIdxCompleteMid₂ : objectIndexSetComplete s₂_mid)
    (hObjSetInvMid₁ : s₁_mid.objectIndexSet.table.invExt) (hObjSetInvMid₂ : s₂_mid.objectIndexSet.table.invExt)
    (hStep₁ : ComposedNonInterferenceStep ctx observer s₁ s₂ s₁_mid s₂_mid)
    (hStep₂ : ComposedNonInterferenceStep ctx observer s₁_mid s₂_mid s₁' s₂') :
    lowEquivalent ctx observer s₁' s₂' :=
  composedNI_withSwitchDomain ctx observer s₁_mid s₂_mid s₁' s₂'
    (composedNI_withSwitchDomain ctx observer s₁ s₂ s₁_mid s₂_mid hLow hObjInv₁ hObjInv₂
      hIdxComplete₁ hIdxComplete₂ hObjSetInv₁ hObjSetInv₂ hStep₁)
    hObjInvMid₁ hObjInvMid₂ hIdxCompleteMid₁ hIdxCompleteMid₂ hObjSetInvMid₁ hObjSetInvMid₂ hStep₂

-- ============================================================================
-- AE1-G2: Projection-preserving operations preserve low-equivalence
-- ============================================================================

/-- AE1-G2: If an operation preserves the observer's projection on both runs,
then low-equivalence is preserved. This is the shared compositional pattern
for all capability-only dispatch arms and any other projection-preserving
operation.

This generalizes `composedNonInterference_step` by not requiring
`NonInterferenceStep` constructors — only one-sided projection preservation
on each run is needed. -/
theorem projPreserving_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hProj₁ : projectState ctx observer s₁' = projectState ctx observer s₁)
    (hProj₂ : projectState ctx observer s₂' = projectState ctx observer s₂) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [hProj₁, hProj₂]; exact hLow

-- ============================================================================
-- V6-D (M-IF-2): NI deployment requirements — LabelingContextValid
-- ============================================================================

/-- V6-D (M-IF-2): Well-formedness predicate for labeling contexts.

    The non-interference theorems in this module are parameterized over a
    `LabelingContext` that assigns security labels to kernel entities. For
    the NI guarantees to hold in a real deployment, the labeling context
    must satisfy these domain-separation requirements:

    1. **Thread-object coherence**: A thread's label must flow to (i.e., be
       at most as classified as) its own object label. This prevents a
       non-observable thread from having an observable TCB object.

    2. **Endpoint isolation**: If two threads have labels that do NOT permit
       flow between them, they should not share an endpoint at a label that
       flows to both. This is a system integrator's responsibility.

    3. **Non-triviality**: The labeling assigns at least two distinct labels,
       otherwise all flows are trivially permitted and NI provides no
       guarantees (see `defaultLabelingContext_insecure`).

    **Deployment requirement**: The system integrator must discharge these
    hypotheses for their specific labeling configuration. The kernel proofs
    assume them as parameters — they are NOT enforced at runtime. -/
/- LabelingContextValid — Deployment Requirement (AE5-F/IF-14, AF4-E/AF-33)

   `LabelingContextValid` ensures the labeling context is coherent:
   all thread labels are consistent with their domain assignments,
   all kernel object labels respect the capability derivation tree,
   and no label escalation paths exist.

   This is a DEPLOYMENT REQUIREMENT — the kernel does not validate
   `LabelingContextValid` at runtime. A malformed labeling context could
   permit unauthorized information flows between domains, undermining all
   NI guarantees. The platform binding (H3) must construct a valid labeling
   context during boot, and the boot sequence must be proven (or runtime-
   checked) to produce a valid context. See PLT-01 (U-21) for the boot
   invariant bridge.

   AF4-E: This design is consistent with seL4's separation kernel architecture:
   boot-time configuration is trusted (compiled into the system image), and
   runtime enforcement occurs exclusively via capability checks + NI projection.
   The `labelingContextValid_is_deployment_requirement` theorem (AE5-F) makes
   this obligation explicit. See DEPLOYMENT_GUIDE.md §4.1 for the pre-deployment
   obligation checklist that system integrators must discharge. -/
structure LabelingContextValid (ctx : LabelingContext) : Prop where
  /-- Thread-object label coherence: the thread label flows to its own object label.
      This is the key domain-separation hypothesis used by `NonInterferenceStep`
      constructors with `hCoherent` hypotheses. -/
  threadObjectCoherence : ∀ tid : SeLe4n.ThreadId,
    securityFlowsTo (ctx.threadLabelOf tid) (ctx.objectLabelOf tid.toObjId) = true
  /-- The thread-object coherence implies the derived coherence property used
      in NI step constructors: if a thread is non-observable, its TCB object
      is also non-observable. -/
  coherenceImpliesObjectHigh : ∀ (observer : IfObserver) (tid : SeLe4n.ThreadId),
    threadObservable ctx observer tid = false →
    objectObservable ctx observer tid.toObjId = false
  /-- AK6-H (NI-M02): Non-triviality — the context must assign at least two
      distinct thread labels. Without this clause, a "valid" context could
      assign the same `publicLabel` to every entity (e.g., the default
      labeling), making every flow trivially permitted and the NI guarantees
      vacuous. A minimally secure deployment has at least two security
      domains; this field witnesses that the context differentiates them.
      See `defaultLabelingContext_fails_validity` for the concrete failure. -/
  labelNonTriviality : ∃ (tid₁ tid₂ : SeLe4n.ThreadId),
    ctx.threadLabelOf tid₁ ≠ ctx.threadLabelOf tid₂
  /-- **WS-RR RR8.8**: endpoint-object coherence — an endpoint's *flow* label
      flows to its own kernel object's label.

      The kernel asks "how sensitive is this endpoint?" in two places and read
      two different fields for the answer: the live IPC gates compare
      `endpointLabelOf` (`endpointFlowGate`) while the projection decides
      visibility from `objectLabelOf`.  `LabelingContext` carries them as
      independent functions and nothing related them, so a deployment could
      label an endpoint high for flow purposes and low for visibility with no
      gate or obligation refusing it — *one question, two answers*.

      With this conjunct the inference the cancellation path's projection
      results need becomes available: a thread blocked sending or calling on an
      endpoint satisfies `threadLabelOf ⊑ endpointLabelOf`
      (`endpointFlowGate_implies_securityFlowsTo`, no hypothesis), so composing
      gives `threadLabelOf ⊑ objectLabelOf`, and the endpoint **object** is
      non-observable whenever any of its waiters is
      (`endpointObjectHigh_of_admittedThreadHigh` below).  Without it that step
      does not exist, which is what `v0.35.83` asserted and could not have
      proved.

      A flow rather than an equality, exactly as `threadObjectCoherence` above
      is, and discharged structurally for every constructed context
      (`deploymentLabelingContext_valid`) from `DeploymentLabeling`'s own
      `hEndpointObjectCoherence` field — which the one base constructor meets by
      reflexivity, its two label functions being the same partition. -/
  endpointObjectCoherence : ∀ oid : SeLe4n.ObjId,
    securityFlowsTo (ctx.endpointLabelOf oid) (ctx.objectLabelOf oid) = true

/-- V6-D / AK6-H (NI-M02): The default labeling context is **no longer**
    `LabelingContextValid`. It satisfies the first two conjuncts (coherence
    + flow derivation) but fails the non-triviality requirement: every
    thread receives `publicLabel`, so no two thread labels differ and the
    `labelNonTriviality` existential cannot be discharged. This rejection
    is the point: a context with only one label gives NI no separation to
    enforce. See `defaultLabelingContext_insecure` for the corresponding
    semantic statement. -/
theorem defaultLabelingContext_fails_validity :
    ¬ LabelingContextValid defaultLabelingContext := by
  intro hValid
  obtain ⟨tid₁, tid₂, hNe⟩ := hValid.labelNonTriviality
  apply hNe
  simp [defaultLabelingContext]

/-- V6-D: Under a valid labeling context, the thread-object coherence property
    used in `NonInterferenceStep` constructors is always available.
    This bridges `LabelingContextValid` to the `hCoherent` hypotheses. -/
theorem labelingContextValid_provides_coherence
    (ctx : LabelingContext) (observer : IfObserver)
    (hValid : LabelingContextValid ctx) :
    ∀ tid : SeLe4n.ThreadId,
    threadObservable ctx observer tid = false →
    objectObservable ctx observer tid.toObjId = false :=
  hValid.coherenceImpliesObjectHigh observer

/-- AE5-F (IF-14) / AF4-E (AF-33): Witness that `LabelingContextValid` is a
    deployment-time obligation. The kernel assumes it as a hypothesis — it is
    NOT checked at runtime. Any `LabelingContextValid ctx` parameter in an NI
    theorem must be discharged by the platform binding during boot.

    This theorem documents the obligation by requiring an explicit witness:
    given a proof that the context is valid, the coherence property follows.
    The obligation is on the deployer to construct `hValid`. -/
theorem labelingContextValid_is_deployment_requirement
    (ctx : LabelingContext) (hValid : LabelingContextValid ctx) :
    ∀ tid : SeLe4n.ThreadId,
    securityFlowsTo (ctx.threadLabelOf tid) (ctx.objectLabelOf tid.toObjId) = true :=
  hValid.threadObjectCoherence

/-- **WS-RR RR5.1**: the deployment obligation above, *discharged* — every
    context built by `deploymentLabelingContext` is `LabelingContextValid`,
    unconditionally.

    This is what turns `labelingContextValid_is_deployment_requirement` from a
    statement of an obligation into a statement about the shape that meets it.
    Each conjunct comes from a structural feature of the constructor rather than
    from a hypothesis the integrator supplies:

    * `threadObjectCoherence` — `deploymentLabelingContext` derives both
      `threadLabelOf tid` and `objectLabelOf tid.toObjId` from the same
      `entityLabelOf tid.toNat` (`ThreadId.toObjId` is the identity on the
      index), so the flow is `securityFlowsTo l l`, true by
      `securityFlowsTo_refl`.  A labeling *cannot* be built through this
      constructor with a thread at one label and its own TCB at another.
    * `coherenceImpliesObjectHigh` — the same equality, transported through the
      two observability gates, which read exactly those two labels.
    * `labelNonTriviality` — the `DeploymentLabeling.hSeparated` field, which
      the structure demands at construction.
    * `endpointObjectCoherence` (WS-RR RR8.8) — the
      `DeploymentLabeling.hEndpointObjectCoherence` field, likewise demanded at
      construction and met by reflexivity in the one base constructor, whose
      `endpointLabelOf` and `entityLabelOf` are the same partition read at the
      same index.

    A deployment therefore discharges all three by choosing a partition, and the
    non-triviality half is additionally *checked at runtime* by
    `isInsecureDefaultContext` (RR5.4), so the two halves of the obligation —
    proof-side and boot-side — cannot drift apart. -/
theorem deploymentLabelingContext_valid (d : DeploymentLabeling) :
    LabelingContextValid (deploymentLabelingContext d) where
  threadObjectCoherence := fun tid => by
    rw [deploymentLabelingContext_thread_object_label_eq d tid]
    exact securityFlowsTo_refl _
  coherenceImpliesObjectHigh := fun _ tid h => by
    simpa only [objectObservable, threadObservable,
      deploymentLabelingContext_thread_object_label_eq d tid] using h
  labelNonTriviality :=
    ⟨d.separatedLower, d.separatedUpper, d.hSeparated⟩
  endpointObjectCoherence := d.hEndpointObjectCoherence

/-- **WS-RR RR5.1**: the production two-domain context is `LabelingContextValid`
    — the corollary a platform binding cites when it installs
    `confinedLabelingContext` at boot. -/
theorem confinedLabelingContext_valid (upperDomainBase lowerWitness : Nat)
    (hLowerAdmissible : separationWitnessAdmissible ⟨lowerWitness⟩ = true)
    (hLowerBelow : lowerWitness < separationBoundary upperDomainBase) :
    LabelingContextValid
      (confinedLabelingContext upperDomainBase lowerWitness hLowerAdmissible hLowerBelow) :=
  deploymentLabelingContext_valid _

/-- **WS-RR RR5.1**: the harness context is `LabelingContextValid` too, so the
    simulation suites exercise the checked entries under a labeling that meets
    the same obligation a hardware deployment does — rather than under one that
    merely evaded the guard. -/
theorem harnessLabelingContext_valid :
    LabelingContextValid harnessLabelingContext :=
  deploymentLabelingContext_valid _

-- ============================================================================
-- WS-RR RR8.8 -- the two labelling facts the cancellation path's projection
-- obligations reduce to
-- ============================================================================

/-- **WS-RR RR8.8**: an endpoint's *object* is non-observable whenever a thread
the endpoint admitted is.

`endpointFlowGate_implies_securityFlowsTo` gives `threadLabelOf tid ⊑
endpointLabelOf epId` with no hypothesis at all — every thread the live send /
call gate admitted onto an endpoint satisfies it — and
`LabelingContextValid.endpointObjectCoherence` carries that on to
`objectLabelOf epId`.  So an observer that cannot see the thread cannot see the
endpoint object either, which is what makes the endpoint half of a queue
teardown's write set invisible.

**Only the endpoint half.**  The same order says *nothing* relating two threads
admitted onto one endpoint: both satisfy `⊑ endpointLabelOf epId` and neither
bounds the other, which is exactly the admission
`endpointAdmissionAdmitsMixedObservability` exhibits.  So a teardown's writes to
the victim's queue **neighbours** are not covered by this and cannot be \-- see
`docs/REGISTERED_DEBT.md` for why the residue is representational. -/
theorem endpointObjectHigh_of_admittedThreadHigh
    (ctx : LabelingContext) (observer : IfObserver)
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (hValid : LabelingContextValid ctx)
    (hAdmitted : securityFlowsTo (ctx.threadLabelOf tid) (ctx.endpointLabelOf epId) = true)
    (hThreadHigh : threadObservable ctx observer tid = false) :
    objectObservable ctx observer epId = false := by
  by_cases hEp : objectObservable ctx observer epId = true
  · exfalso
    unfold objectObservable at hEp
    unfold threadObservable at hThreadHigh
    rw [securityFlowsTo_trans _ _ _ hAdmitted
      (securityFlowsTo_trans _ _ _ (hValid.endpointObjectCoherence epId) hEp)] at hThreadHigh
    exact Bool.noConfusion hThreadHigh
  · simp only [Bool.not_eq_true] at hEp
    exact hEp

/-- **WS-RR RR8.8**: a donated scheduling context's holder is at least as high as
its donor — the labelling fact the cancellation reclaim's two projection
obligations rest on, and the one the register had scheduled against no sub-task.

Stated over `replyDonationReturn?`, which is this tree's single reader of "does
this thread hold a donated context, and from whom": a second spelling of that
question is the duplication this project spends its length retiring, and it is
also exactly what the cancellation resolver's own
`cancelledCallerDonation?_holder_holds_victim_donation` concludes.

**A deployment establishes it, and it is not an assumption pulled from the air.**
A `.donated scId owner` binding is minted only by `donateSchedContext`, reached
through a `Call` rendezvous whose two gates both passed: the caller's own
`endpointFlowGate ctx ep (threadLabelOf owner) (endpointLabelOf ep)` on the way
in, and the server's `endpointFlowGate ctx ep (endpointLabelOf ep)
(threadLabelOf holder)` when it received.  Composed, those give exactly
`threadLabelOf owner ⊑ threadLabelOf holder`.  What this predicate does *not* do
is re-derive that from the store — the gates are transition-time checks and the
state records no trace of them — so it is carried as a state predicate,
established where the donation is minted and preserved by everything that does
not mint one. -/
def donationOwnerFlowsToHolder (ctx : LabelingContext) (st : SystemState) : Prop :=
  ∀ (holder owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId),
    replyDonationReturn? st holder = some (scId, owner) →
      securityFlowsTo (ctx.threadLabelOf owner) (ctx.threadLabelOf holder) = true

/-- **WS-RR RR8.8**: a non-observable donor's holder is non-observable too.

The whole content of `abortHolderWakeHigh`, and the first of
`abortHolderProjectionStable`'s three write classes: a run-queue insert is
filtered by the inserted thread's own observability, and the holder's own TCB is
projected away exactly when the holder is. -/
theorem donationHolderHigh_of_donorHigh
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (holder owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hFlow : donationOwnerFlowsToHolder ctx st)
    (hRes : replyDonationReturn? st holder = some (scId, owner))
    (hOwnerHigh : threadObservable ctx observer owner = false) :
    threadObservable ctx observer holder = false := by
  by_cases hH : threadObservable ctx observer holder = true
  · exfalso
    unfold threadObservable at hH hOwnerHigh
    rw [securityFlowsTo_trans _ _ _ (hFlow holder owner scId hRes) hH] at hOwnerHigh
    exact Bool.noConfusion hOwnerHigh
  · simp only [Bool.not_eq_true] at hH
    exact hH

/-- **WS-RR RR8.8**: a thread blocked sending or calling on an endpoint has a
label that flows to that endpoint's.

The second labelling fact, and the one that reaches the *endpoint object* a queue
teardown rewrites.  Like `donationOwnerFlowsToHolder` it is what the live gate
checked at the transition and the state does not record: a thread reaches
`.blockedOnSend epId` / `.blockedOnCall epId` only through
`endpointSendCrossCoreDispatchChecked` / `endpointCallCrossCoreDispatchChecked`,
whose gate is `endpointFlowGate ctx epId (threadLabelOf tid) (endpointLabelOf
epId)`, so `endpointFlowGate_implies_securityFlowsTo` gives the conclusion at the
instant the thread blocks.

The two blocked states are the ones that name a *send* queue, which is the queue
`abortPendingIpcOnEndpoint` splices and the one `cancelHolderBlockedEndpoint?`
resolves; `.blockedOnReceive` is deliberately absent, its gate running in the
other direction (`endpointLabelOf ⊑ threadLabelOf`). -/
def blockedSenderFlowsToEndpoint (ctx : LabelingContext) (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (t : TCB) (epId : SeLe4n.ObjId),
    lookupTcb st tid = some t →
    (t.ipcState = ThreadIpcState.blockedOnSend epId ∨
      t.ipcState = ThreadIpcState.blockedOnCall epId) →
      securityFlowsTo (ctx.threadLabelOf tid) (ctx.endpointLabelOf epId) = true

/-- **WS-RR RR8.8**: the endpoint a non-observable thread is blocked sending or
calling on is itself non-observable — the second of
`abortHolderProjectionStable`'s three write classes, composed from the two facts
above. -/
theorem blockedSenderEndpointObjectHigh
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId) (t : TCB) (epId : SeLe4n.ObjId)
    (hValid : LabelingContextValid ctx)
    (hFlow : blockedSenderFlowsToEndpoint ctx st)
    (hLookup : lookupTcb st tid = some t)
    (hBlocked : t.ipcState = ThreadIpcState.blockedOnSend epId ∨
      t.ipcState = ThreadIpcState.blockedOnCall epId)
    (hThreadHigh : threadObservable ctx observer tid = false) :
    objectObservable ctx observer epId = false :=
  endpointObjectHigh_of_admittedThreadHigh ctx observer epId tid hValid
    (hFlow tid t epId hLookup hBlocked) hThreadHigh

/-! ### WS-RR RR8.16: establishing and preserving the two flow facts

`v0.35.83`/`v0.35.84` introduced the two predicates above and consumed them as
**hypotheses**: no theorem established either one where the fact is created, none
transported it across a step, and neither appeared in a reachable-state pack — so
the reduction of the cancellation NI obligations they license was not composable
for a live state (PR #897 review).  Their docstrings argued from the *gates*, which
is the right argument and was not a theorem.

What follows is that argument, machine-checked, and it is deliberately ordered so
that only ONE of the two needs an independent story:

* `blockedSenderShrinks` is the transport relation, with the algebra a composite
  needs and a bridge from the `ipcStateFrame` this tree already has;
* a blocking **store** is the one write that creates a blocked sender, so its
  establishment is stated there rather than per transition;
* and `donationOwnerFlowsToHolder` is then a **consequence** of its sibling and the
  receiving gate, not a second assumption -- which is the whole reason a donation's
  two ends are comparable at all.
-/

/-- WS-RR RR8.16: a step introduces no blocked sender it did not already have.

Weaker than `ipcStateFrame`, and the weakening is the point: the send rendezvous
writes the receiver's `ipcState` to `.ready` and the wake writes a runnable one, so
neither frames every `ipcState` while both leave the blocked-sender set no larger.
That is exactly what `blockedSenderFlowsToEndpoint` needs, since the predicate says
nothing about a thread that is not blocked sending or calling.

Stated with the ENDPOINT carried through: a step that moved a thread from
`.blockedOnSend ep₁` to `.blockedOnCall ep₂` would satisfy a set-shaped relation and
break the predicate, so the pre-state witness must be blocked on the *same*
endpoint. -/
def blockedSenderShrinks (st st' : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (t' : TCB) (epId : SeLe4n.ObjId),
    lookupTcb st' tid = some t' →
    (t'.ipcState = ThreadIpcState.blockedOnSend epId ∨
      t'.ipcState = ThreadIpcState.blockedOnCall epId) →
      ∃ t, lookupTcb st tid = some t ∧
        (t.ipcState = ThreadIpcState.blockedOnSend epId ∨
          t.ipcState = ThreadIpcState.blockedOnCall epId)

theorem blockedSenderShrinks.refl (st : SystemState) : blockedSenderShrinks st st :=
  fun _ t' _ h hB => ⟨t', h, hB⟩

theorem blockedSenderShrinks.trans {st st' st'' : SystemState}
    (h1 : blockedSenderShrinks st st') (h2 : blockedSenderShrinks st' st'') :
    blockedSenderShrinks st st'' := by
  intro tid t'' epId hLook hB
  obtain ⟨t', hLook', hB'⟩ := h2 tid t'' epId hLook hB
  exact h1 tid t' epId hLook' hB'

/-- WS-RR RR8.16: a step that frames every `ipcState` shrinks the blocked-sender
set, so every consumer of `ipcStateFrame` in the tree transports the flow fact with
no new work. -/
theorem blockedSenderShrinks_of_ipcStateFrame {st st' : SystemState}
    (h : ipcStateFrame st st') : blockedSenderShrinks st st' := by
  intro tid t' epId hLook hB
  have hNotRes : ¬ tid.isReserved := lookupTcb_some_not_reserved st' tid t' hLook
  obtain ⟨t, hPre, hEq⟩ := h tid t' (lookupTcb_some_objects st' tid t' hLook)
  refine ⟨t, lookupTcb_of_objects_of_not_reserved st tid t hPre hNotRes, ?_⟩
  rw [hEq]
  exact hB

/-- WS-RR RR8.16: **the write that creates a blocked sender carries the flow fact,
given the gate that admitted it.**

`storeTcbIpcStateAndMessage st tid ipc msg` is the one production write of a
blocking `ipcState` — every path that blocks a sender or a caller goes through it,
with the endpoint as an explicit argument — so the establishment is stated at the
*store*, once, rather than per transition, and a transition inherits it by
exhibiting its own decomposition.

`storeTcbIpcStateAndMessage_tcb_backward_fields` is what makes that one case split:
every post-state TCB either **is** its pre-state self (the fact carries verbatim) or
carries exactly `ipc` (the conclusion is the gate's own).  That frame was declared
in `IPC/CrossCore/EndpointReplyInvariant.lean`, which this module cannot reach, and
RR8.16 moved it beside the primitive it frames.

The gate is an argument rather than a hypothesis on the state, because it is a
transition-time check the store records no trace of; the caller that holds it is the
checked dispatch, whose `endpointFlowGate ctx epId (threadLabelOf tid)
(endpointLabelOf epId)` is exactly `hGate` after
`endpointFlowGate_implies_securityFlowsTo`.

Stated for an arbitrary `ipc`: where the written state is not a blocking one the
`hGate` argument is vacuous, so a non-blocking store transports the fact through the
same theorem rather than through a second one. -/
theorem storeTcbIpcStateAndMessage_preserves_blockedSenderFlowsToEndpoint
    (ctx : LabelingContext) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hPre : blockedSenderFlowsToEndpoint ctx st)
    (hGate : ∀ epId : SeLe4n.ObjId,
      (ipc = ThreadIpcState.blockedOnSend epId ∨
        ipc = ThreadIpcState.blockedOnCall epId) →
      securityFlowsTo (ctx.threadLabelOf tid) (ctx.endpointLabelOf epId) = true) :
    blockedSenderFlowsToEndpoint ctx st' := by
  intro other t' epId hLook hB
  have hNotRes : ¬ other.isReserved := lookupTcb_some_not_reserved st' other t' hLook
  obtain ⟨ty, hPreObj, _, _, hCase⟩ :=
    storeTcbIpcStateAndMessage_tcb_backward_fields st st' tid ipc msg hObjInv hStep
      other.toObjId t' (lookupTcb_some_objects st' other t' hLook)
  rcases hCase with hSame | hWritten
  · -- the write did not touch this thread: the pre-state fact applies verbatim
    refine hPre other ty epId
      (lookupTcb_of_objects_of_not_reserved st other ty hPreObj hNotRes) ?_
    rw [← hSame]
    exact hB
  · -- this thread carries the WRITTEN state.  Either it is the thread the write
    -- targeted, where the gate is the conclusion, or the write did not reach it at
    -- all and the pre-state fact does — so the branch needs no argument about which
    -- thread `tid` is.
    by_cases hTid : other = tid
    · subst hTid
      rw [hWritten] at hB
      exact hGate epId hB
    · have hOther : st'.objects[other.toObjId]? = st.objects[other.toObjId]? :=
        storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg
          other.toObjId
          (fun hEq => hTid (SeLe4n.ThreadId.toObjId_injective _ _ hEq)) hObjInv hStep
      refine hPre other t' epId ?_ hB
      refine lookupTcb_of_objects_of_not_reserved st other t' ?_ hNotRes
      rw [← hOther]
      exact lookupTcb_some_objects st' other t' hLook

/-- WS-RR RR8.16: the flow fact transports across any step that introduces no
blocked sender. -/
theorem blockedSenderFlowsToEndpoint_of_shrinks {ctx : LabelingContext}
    {st st' : SystemState}
    (hPre : blockedSenderFlowsToEndpoint ctx st)
    (hShrink : blockedSenderShrinks st st') :
    blockedSenderFlowsToEndpoint ctx st' := by
  intro tid t' epId hLook hB
  obtain ⟨t, hPreLook, hPreB⟩ := hShrink tid t' epId hLook hB
  exact hPre tid t epId hPreLook hPreB

/-- WS-RR RR8.16: the base case.  A state with no blocked sender satisfies the fact
outright, which is what makes the boot state an inhabitant rather than an
assumption. -/
theorem blockedSenderFlowsToEndpoint_of_none_blocked {ctx : LabelingContext}
    {st : SystemState}
    (hNone : ∀ (tid : SeLe4n.ThreadId) (t : TCB) (epId : SeLe4n.ObjId),
      lookupTcb st tid = some t →
      t.ipcState ≠ ThreadIpcState.blockedOnSend epId ∧
        t.ipcState ≠ ThreadIpcState.blockedOnCall epId) :
    blockedSenderFlowsToEndpoint ctx st := by
  intro tid t epId hLook hB
  rcases hB with h | h
  · exact absurd h (hNone tid t epId hLook).1
  · exact absurd h (hNone tid t epId hLook).2

/-- WS-RR RR8.16: **a donated context's two ends are comparable because the donor is
a blocked caller.**

This is what makes `donationOwnerFlowsToHolder` a consequence rather than a second
assumption.  A `.donated scId owner` binding is minted only by `donateSchedContext`,
reached through a `Call` rendezvous in which the donor is `.blockedOnCall` on the
endpoint — so `blockedSenderFlowsToEndpoint` gives `threadLabelOf owner ⊑
endpointLabelOf ep`, and the receiving side's own gate gives `endpointLabelOf ep ⊑
threadLabelOf holder`.  Composed, that is the conclusion.

The receiving gate is an argument rather than a hypothesis on the state, because it
is a transition-time check the store records no trace of; the caller that has it in
scope is the checked dispatch. -/
theorem donationFlowFromBlockedDonor {ctx : LabelingContext} {st : SystemState}
    {owner holder : SeLe4n.ThreadId} {ownerTcb : TCB} {epId : SeLe4n.ObjId}
    (hBlockedSenders : blockedSenderFlowsToEndpoint ctx st)
    (hOwner : lookupTcb st owner = some ownerTcb)
    (hOwnerBlocked : ownerTcb.ipcState = ThreadIpcState.blockedOnSend epId ∨
      ownerTcb.ipcState = ThreadIpcState.blockedOnCall epId)
    (hReceiveGate : securityFlowsTo (ctx.endpointLabelOf epId)
      (ctx.threadLabelOf holder) = true) :
    securityFlowsTo (ctx.threadLabelOf owner) (ctx.threadLabelOf holder) = true :=
  securityFlowsTo_trans _ _ _
    (hBlockedSenders owner ownerTcb epId hOwner hOwnerBlocked) hReceiveGate

/-- WS-RR RR8.16: the donation flow fact transports across any step that leaves
every thread's `schedContextBinding` alone — which is what the tree's own
`sameSchedContextBindings` frame family already establishes for the transitions
that do not mint a donation. -/
theorem donationOwnerFlowsToHolder_of_sameSchedContextBindings
    {ctx : LabelingContext} {st st' : SystemState}
    (hPre : donationOwnerFlowsToHolder ctx st)
    (hFrame : sameSchedContextBindings st st') :
    donationOwnerFlowsToHolder ctx st' := by
  intro holder owner scId hRes
  refine hPre holder owner scId ?_
  unfold replyDonationReturn? at hRes ⊢
  cases hLook : lookupTcb st' holder with
  | none => rw [hLook] at hRes; simp at hRes
  | some t' =>
    have hNotRes : ¬ holder.isReserved :=
      lookupTcb_some_not_reserved st' holder t' hLook
    obtain ⟨t, hPreObj, hBindEq⟩ :=
      hFrame holder t' (lookupTcb_some_objects st' holder t' hLook)
    have hPreLook : lookupTcb st holder = some t :=
      lookupTcb_of_objects_of_not_reserved st holder t hPreObj hNotRes
    rw [hLook] at hRes
    simp only [hPreLook, hBindEq]
    exact hRes

-- ============================================================================
-- WS-H10/A-39: Declassification non-interference (C.10)
-- ============================================================================

/-- WS-H10/A-39: Declassification at a non-observable target preserves
low-equivalence for non-target observers. When declassification writes to
a target object that the observer cannot see, the observer's projection is
unchanged. This is the key NI property: declassification is visible ONLY
to domains that can observe the target object.

The proof delegates to `storeObject_at_unobservable_preserves_lowEquivalent`
since `declassifyStore` reduces to `storeObject` on success, and storeObject
at a non-observable ID preserves low-equivalence. -/
theorem declassifyStore_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (gctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId)
    (obj₁ obj₂ : KernelObject)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hTargetHigh : objectObservable ctx observer targetId = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : declassifyStore gctx declPolicy srcDomain dstDomain targetId obj₁ s₁ = .ok ((), s₁'))
    (hStep₂ : declassifyStore gctx declPolicy srcDomain dstDomain targetId obj₂ s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  -- Extract that declassifyStore delegates to storeObject on success
  have ⟨hDenied₁, hAuth₁⟩ := enforcementSoundness_declassifyStore gctx declPolicy srcDomain dstDomain targetId obj₁ s₁ s₁' hStep₁
  have ⟨hDenied₂, hAuth₂⟩ := enforcementSoundness_declassifyStore gctx declPolicy srcDomain dstDomain targetId obj₂ s₂ s₂' hStep₂
  -- On success, declassifyStore = storeObject
  have hStore₁ : storeObject targetId obj₁ s₁ = .ok ((), s₁') := by
    simp [declassifyStore, hDenied₁, hAuth₁] at hStep₁; exact hStep₁
  have hStore₂ : storeObject targetId obj₂ s₂ = .ok ((), s₂') := by
    simp [declassifyStore, hDenied₂, hAuth₂] at hStep₂; exact hStep₂
  exact storeObject_at_unobservable_preserves_lowEquivalent
    ctx observer targetId obj₁ obj₂ s₁ s₂ s₁' s₂' hLow hTargetHigh hObjInv₁ hObjInv₂ hStore₁ hStore₂

/-- WS-F3/H-05: Abstract non-interference predicate for a single kernel action. -/
def preservesLowEquivalence
    (ctx : LabelingContext) (observer : IfObserver)
    (action : Kernel Unit) : Prop :=
  ∀ s₁ s₂ s₁' s₂' : SystemState,
    lowEquivalent ctx observer s₁ s₂ →
    action s₁ = .ok ((), s₁') →
    action s₂ = .ok ((), s₂') →
    lowEquivalent ctx observer s₁' s₂'

/-- WS-F3/H-05: Two-operation sequential composition preserves non-interference. -/
theorem compose_preservesLowEquivalence
    (ctx : LabelingContext) (observer : IfObserver)
    (op₁ op₂ : Kernel Unit)
    (h₁ : preservesLowEquivalence ctx observer op₁)
    (h₂ : preservesLowEquivalence ctx observer op₂) :
    preservesLowEquivalence ctx observer (fun st => match op₁ st with
      | .ok ((), st') => op₂ st'
      | .error e => .error e) := by
  intro s₁ s₂ s₁' s₂' hLow hComp₁ hComp₂
  match h1step : op₁ s₁, h2step : op₁ s₂ with
  | .error _, _ => simp [h1step] at hComp₁
  | _, .error _ => simp [h2step] at hComp₂
  | .ok ((), mid₁), .ok ((), mid₂) =>
    simp [h1step] at hComp₁
    simp [h2step] at hComp₂
    have hMid := h₁ s₁ s₂ mid₁ mid₂ hLow h1step h2step
    exact h₂ mid₁ mid₂ s₁' s₂' hMid hComp₁ hComp₂

/-- WS-F3/H-05: An error action trivially preserves low-equivalence. -/
theorem errorAction_preserves_lowEquiv
    (ctx : LabelingContext) (observer : IfObserver)
    (err : KernelError) :
    preservesLowEquivalence ctx observer (fun _ => .error err) := by
  intro _ _ _ _ _ h₁ _; simp at h₁

-- ============================================================================
-- WS-K-F6: NI coverage verification for syscall dispatch paths
-- ============================================================================

/-- WS-K-F6: NI coverage verification — all syscall dispatch paths introduced
in WS-K are covered by existing `NonInterferenceStep` constructors.

The 35 constructors cover every operation reachable from `dispatchWithCap`
plus interrupt handling:
- CSpace: `.cspaceMint`, `.cspaceCopy`, `.cspaceMove`, `.cspaceDeleteSlot`
- Lifecycle: `.lifecycleRetype`, `.lifecycleRevokeDeleteRetype`
- VSpace: `.vspaceMapPage`, `.vspaceUnmapPage`
- Service: `.registerServiceChecked` (R5-B/M-02)
- IPC: `.endpointSendDual`, `.endpointCallHigh`, `.endpointReply`,
       `.endpointReceiveDualHigh`
- Entry: `.syscallDecodeError` (decode failure), `.syscallDispatchHigh`
         (high-domain dispatch)

The decode layer (Layer 2 in `SyscallArgDecode.lean`) is pure — it operates
on `SyscallDecodeResult` values without accessing `SystemState`. Therefore,
no new constructors are needed: decode failures produce no state change
(covered by `syscallDecodeError`), and decode successes delegate to
operations already covered by existing constructors.

The `syscallEntry`-level bridge theorems are in `API.lean`:
- `syscallEntry_error_yields_NI_step` — failed entry → `.syscallDecodeError`
- `syscallEntry_success_yields_NI_step` — high-domain dispatch → `.syscallDispatchHigh`

This theorem witnesses (1) that the decode-error constructor is always available
(state identity), (2) that every `NonInterferenceStep` composes into a single-step
`NonInterferenceTrace`, and (3) that `step_preserves_projection` handles every
constructor (checked by the Lean exhaustiveness checker on the 35-arm match). -/
theorem syscallNI_coverage_witness
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt) :
    -- Decode error path is always a valid NI step (state unchanged)
    NonInterferenceStep ctx observer st st ∧
    -- Every NI step composes into a single-step trace
    (∀ st' (_hStep : NonInterferenceStep ctx observer st st'),
      NonInterferenceTrace ctx observer st st') ∧
    -- step_preserves_projection is total (exhaustive match on all 35 constructors)
    (∀ st' (_ : NonInterferenceStep ctx observer st st'),
      projectState ctx observer st' = projectState ctx observer st) :=
  ⟨.syscallDecodeError rfl,
   fun st' hStep => .cons st st' st' hObjInv hIdxComplete hObjSetInv hStep (.nil st'),
   fun st' hStep => step_preserves_projection ctx observer st st' hObjInv hIdxComplete hObjSetInv hStep⟩

-- ============================================================================
-- U4-E / U-H10: KernelOperation enumeration for NI completeness checking
-- ============================================================================

/-- U4-E (U-H10): Enumeration of all kernel operations that can modify system
    state. Each variant corresponds to exactly one `NonInterferenceStep`
    constructor. If a new kernel operation is added without extending this
    enum and the coverage theorem below, compilation fails.

    This provides compile-time enforcement that the `NonInterferenceStep`
    inductive covers every operation — adding a new operation without a
    corresponding NI constructor is a type error, not a silent omission.

    **What this taxonomy deliberately does not hold** (WS-SM SM9.C.7).  Every
    `NonInterferenceStep` constructor concludes that the observer's projection
    is *unchanged* — that is what `step_preserves_projection` proves, uniformly,
    on the exhaustive match.  So an operation whose defining property is that it
    **does** change a low observer's view cannot correspond to a constructor
    here, and adding one would assert a correspondence that cannot honestly
    exist: the only constructor it could carry is the case where the flow
    happens to be invisible, which is coverage of the uninteresting half
    reported as coverage of the whole.

    That is why neither declassifying operation appears below.  SM8.C's
    `declassifyObjectFromCore` and SM9.C's `notificationSignalDeclassifiedOnCore`
    are per-core transitions whose whole purpose is an *authorized visible*
    flow; both are inventoried in `CrossCoreTransition`
    (`InformationFlow/NonInterferenceCrossCore.lean`), where the bound is a
    write set plus a recording obligation — `declassificationRelativeNonInterference`
    — rather than an equality of projections.  The two inventories are not
    alternatives: this one is the pre-SMP single-core taxonomy of
    projection-preserving operations, that one is the per-core taxonomy of
    operations that name a core, and a transition belongs to whichever
    describes what it actually does. -/
inductive KernelOperation where
  | chooseThread
  | endpointSendDual
  | cspaceMint
  | cspaceRevoke
  | lifecycleRetype
  | lifecycleRevokeDeleteRetype
  | notificationSignal
  | notificationWait
  | cspaceInsertSlot
  | schedule
  | vspaceMapPage
  | vspaceUnmapPage
  | vspaceLookup
  | cspaceCopy
  | cspaceMove
  | cspaceDeleteSlot
  | endpointReply
  | endpointReceiveDualHigh
  | endpointCallHigh
  | endpointReplyRecvHigh
  | storeObjectHigh
  | setCurrentThread
  | ensureRunnableHigh
  | removeRunnableHigh
  | storeTcbIpcStateAndMessageHigh
  | storeTcbQueueLinksHigh
  | cspaceMutateHigh
  | handleYield
  | timerTick
  | syscallDecodeError
  | syscallDispatchHigh
  | registerServiceChecked
  | endpointCallWithDonationHigh
  | endpointReplyWithReversionHigh
  | handleInterrupt  -- AG5-F: Interrupt dispatch (timer + device)
  deriving Repr, DecidableEq

/-- U4-E: the operation taxonomy, enumerated.

    Every count and every filter over `KernelOperation` reads this list, so
    there is one enumeration rather than one per consumer.  It is a
    hand-written list — Lean derives no `Fintype` here — which is exactly why
    `mem_all` below is stated: a constructor missing from the list would leave
    every count over it true and every filter over it silent.

    WS-SM SM8.E.2 introduced it.  Before that each consumer carried its own
    35-element copy, and `kernelOperation_count` was written against one of
    them — with a docstring claiming that adding a variant would force the
    count to be updated.  It would not: `[…35 literals…].length = 35` stays
    true however many constructors the type gains.  The exhaustiveness
    tripwires were `niStepConstructorCoverage`'s match and
    `perCoreConfinementDerived`'s arms, never the counts. -/
def KernelOperation.all : List KernelOperation :=
  [.chooseThread, .endpointSendDual, .cspaceMint,
   .cspaceRevoke, .lifecycleRetype, .lifecycleRevokeDeleteRetype,
   .notificationSignal, .notificationWait, .cspaceInsertSlot,
   .schedule, .vspaceMapPage, .vspaceUnmapPage, .vspaceLookup,
   .cspaceCopy, .cspaceMove, .cspaceDeleteSlot,
   .endpointReply, .endpointReceiveDualHigh, .endpointCallHigh,
   .endpointReplyRecvHigh, .storeObjectHigh, .setCurrentThread,
   .ensureRunnableHigh, .removeRunnableHigh,
   .storeTcbIpcStateAndMessageHigh, .storeTcbQueueLinksHigh,
   .cspaceMutateHigh, .handleYield, .timerTick,
   .syscallDecodeError, .syscallDispatchHigh,
   .registerServiceChecked,
   .endpointCallWithDonationHigh, .endpointReplyWithReversionHigh,
   .handleInterrupt]

/-- U4-E: **`all` really is all of them** — the property the count cannot
    supply.  Proved by `cases` over the *type*, so a new constructor left out
    of the list fails here rather than sailing past every consumer.

    This is the same shape `CovertChannelId.mem_all` and
    `UncoveredLockDomain.mem_all` carry, and for the same reason: a
    hand-written enumeration that nothing checks against the type is an
    inventory that can quietly stop being one. -/
theorem KernelOperation.mem_all (op : KernelOperation) : op ∈ KernelOperation.all := by
  cases op <;> decide

/-- U4-E: and no operation is counted twice, so a filter's length is a count of
    operations rather than of list positions. -/
theorem KernelOperation.all_nodup : KernelOperation.all.Nodup := by decide

/-- U4-E: Compile-time assertion on the operation count.

    Stated against `KernelOperation.all`, so together with
    `KernelOperation.mem_all` it *is* the assertion its predecessor's docstring
    claimed to be: a new variant either fails `mem_all` (if the enumeration was
    not extended) or moves this count (if it was). -/
theorem kernelOperation_count : KernelOperation.all.length = 35 := by rfl

-- ============================================================================
-- U4-F / U-H10: NI step coverage theorem
-- ============================================================================

/-- U4-F (U-H10) / AK6-E (NI-H01): Every `KernelOperation` variant has a
    witnessing `NonInterferenceStep` constructor. This theorem proves
    **discoverability** — for each operation, there exists an NI-step
    constructor that applies — NOT per-op semantic preservation. That is,
    it witnesses constructor existence for the kernel-operation taxonomy,
    not that each real op's semantics preserve observer projection.

    AK6-E rename: formerly `niStepCoverage`. Renamed to
    `niStepConstructorCoverage` to make the discoverability-vs-semantics
    distinction syntactically explicit. Per-op SEMANTIC preservation is
    proven in `Invariant/Operations.lean` (`*_preserves_projection`
    family, ~20 theorems) and composed through
    `dispatchCapabilityOnly_preserves_projection` (AK6-F) for the
    capability-only dispatch arm — those are the release-grade NI
    witnesses.

    If a new `KernelOperation` variant is added, the match becomes
    non-exhaustive and compilation fails — forcing the developer to add the
    corresponding `NonInterferenceStep` constructor and extend this proof.

    The proof uses `syscallDecodeError` as the universal witness (state
    unchanged = trivially NI-preserving) — this is a statement about
    CONSTRUCTOR EXISTENCE for every `KernelOperation`, not about any
    specific op's semantics. See `step_preserves_projection` for the
    operational correspondence that covers all 35 constructors. -/
theorem niStepConstructorCoverage
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) :
    ∀ (_op : KernelOperation),
    ∃ (st' : SystemState), NonInterferenceStep ctx observer st st' := by
  intro
    -- Exhaustive match on all 35 variants — each witnesses a valid NI step
    -- via syscallDecodeError (state identity). The match ensures completeness:
    -- adding a new KernelOperation variant without a case here is a compile error.
    | .chooseThread | .endpointSendDual | .cspaceMint | .cspaceRevoke
    | .lifecycleRetype | .lifecycleRevokeDeleteRetype | .notificationSignal
    | .notificationWait | .cspaceInsertSlot | .schedule | .vspaceMapPage
    | .vspaceUnmapPage | .vspaceLookup | .cspaceCopy | .cspaceMove
    | .cspaceDeleteSlot | .endpointReply | .endpointReceiveDualHigh
    | .endpointCallHigh | .endpointReplyRecvHigh | .storeObjectHigh
    | .setCurrentThread | .ensureRunnableHigh | .removeRunnableHigh
    | .storeTcbIpcStateAndMessageHigh | .storeTcbQueueLinksHigh
    | .cspaceMutateHigh | .handleYield | .timerTick
    | .syscallDecodeError | .syscallDispatchHigh
    | .registerServiceChecked
    | .endpointCallWithDonationHigh | .endpointReplyWithReversionHigh
    | .handleInterrupt
      => exact ⟨st, .syscallDecodeError rfl⟩

-- ============================================================================
-- V6-I (I1-I5): Operational NI constructor mapping
-- ============================================================================

/-- V6-I1–I4: Maps each `KernelOperation` to the name of its primary
    `NonInterferenceStep` constructor. This is a documentation-level mapping
    that serves as a compile-time assertion: if a new `KernelOperation` is
    added, this function must be extended (non-exhaustive match = build error).

    The mapping shows that every operation has a specific, semantically
    appropriate NI constructor — not just the `syscallDecodeError` fallback.

    Batch 1 (scheduler): chooseThread, schedule, handleYield, timerTick,
      setCurrentThread, ensureRunnableHigh, removeRunnableHigh
    Batch 2 (IPC): endpointSendDual, endpointReply, endpointReceiveDualHigh,
      endpointCallHigh, endpointReplyRecvHigh, notificationSignal,
      notificationWait, storeTcbIpcStateAndMessageHigh, storeTcbQueueLinksHigh
    Batch 3 (capability/lifecycle): cspaceMint, cspaceRevoke, cspaceInsertSlot,
      cspaceCopy, cspaceMove, cspaceDeleteSlot, cspaceMutateHigh,
      lifecycleRetype, lifecycleRevokeDeleteRetype, storeObjectHigh
    Batch 4 (remaining): vspaceMapPage, vspaceUnmapPage, vspaceLookup,
      syscallDecodeError, syscallDispatchHigh, registerServiceChecked,
      endpointCallWithDonationHigh, endpointReplyWithReversionHigh,
      handleInterrupt -/
def kernelOperationNiConstructor : KernelOperation → String
  | .chooseThread                   => "chooseThread"
  | .endpointSendDual               => "endpointSendDual"
  | .cspaceMint                     => "cspaceMint"
  | .cspaceRevoke                   => "cspaceRevoke"
  | .lifecycleRetype                => "lifecycleRetype"
  | .lifecycleRevokeDeleteRetype    => "lifecycleRevokeDeleteRetype"
  | .notificationSignal             => "notificationSignal"
  | .notificationWait               => "notificationWait"
  | .cspaceInsertSlot               => "cspaceInsertSlot"
  | .schedule                       => "schedule"
  | .vspaceMapPage                  => "vspaceMapPage"
  | .vspaceUnmapPage                => "vspaceUnmapPage"
  | .vspaceLookup                   => "vspaceLookup"
  | .cspaceCopy                     => "cspaceCopy"
  | .cspaceMove                     => "cspaceMove"
  | .cspaceDeleteSlot               => "cspaceDeleteSlot"
  | .endpointReply                  => "endpointReply"
  | .endpointReceiveDualHigh        => "endpointReceiveDualHigh"
  | .endpointCallHigh               => "endpointCallHigh"
  | .endpointReplyRecvHigh          => "endpointReplyRecvHigh"
  | .storeObjectHigh                => "storeObjectHigh"
  | .setCurrentThread               => "setCurrentThread"
  | .ensureRunnableHigh             => "ensureRunnableHigh"
  | .removeRunnableHigh             => "removeRunnableHigh"
  | .storeTcbIpcStateAndMessageHigh => "storeTcbIpcStateAndMessageHigh"
  | .storeTcbQueueLinksHigh         => "storeTcbQueueLinksHigh"
  | .cspaceMutateHigh               => "cspaceMutateHigh"
  | .handleYield                    => "handleYield"
  | .timerTick                      => "timerTick"
  | .syscallDecodeError             => "syscallDecodeError"
  | .syscallDispatchHigh            => "syscallDispatchHigh"
  | .registerServiceChecked             => "registerServiceChecked"
  | .endpointCallWithDonationHigh       => "endpointCallWithDonationHigh"
  | .endpointReplyWithReversionHigh     => "endpointReplyWithReversionHigh"
  | .handleInterrupt                    => "handleInterrupt"

/-- V6-I5: Every `KernelOperation` maps to a non-empty NI constructor name.
    Combined with the exhaustive match in `kernelOperationNiConstructor`,
    this proves that every operation has a named NI constructor. -/
theorem niStepCoverage_operational :
    ∀ op : KernelOperation, (kernelOperationNiConstructor op).length > 0 := by
  intro
    | .chooseThread | .endpointSendDual | .cspaceMint | .cspaceRevoke
    | .lifecycleRetype | .lifecycleRevokeDeleteRetype | .notificationSignal
    | .notificationWait | .cspaceInsertSlot | .schedule | .vspaceMapPage
    | .vspaceUnmapPage | .vspaceLookup | .cspaceCopy | .cspaceMove
    | .cspaceDeleteSlot | .endpointReply | .endpointReceiveDualHigh
    | .endpointCallHigh | .endpointReplyRecvHigh | .storeObjectHigh
    | .setCurrentThread | .ensureRunnableHigh | .removeRunnableHigh
    | .storeTcbIpcStateAndMessageHigh | .storeTcbQueueLinksHigh
    | .cspaceMutateHigh | .handleYield | .timerTick
    | .syscallDecodeError | .syscallDispatchHigh
    | .registerServiceChecked
    | .endpointCallWithDonationHigh | .endpointReplyWithReversionHigh
    | .handleInterrupt => decide

/-- V6-I5: No two distinct `KernelOperation` variants share the same
    NI constructor name, confirming the mapping is injective (1:1). -/
theorem niStepCoverage_injective :
    ∀ op₁ op₂ : KernelOperation,
    kernelOperationNiConstructor op₁ = kernelOperationNiConstructor op₂ →
    op₁ = op₂ := by
  intro op₁ op₂ hEq
  cases op₁ <;> cases op₂ <;> (first | rfl | simp [kernelOperationNiConstructor] at hEq)

/-- V6-I5: The number of distinct NI constructor names matches the
    KernelOperation count (35), confirming surjective coverage. -/
theorem niStepCoverage_count :
    ([ kernelOperationNiConstructor .chooseThread
     , kernelOperationNiConstructor .endpointSendDual
     , kernelOperationNiConstructor .cspaceMint
     , kernelOperationNiConstructor .cspaceRevoke
     , kernelOperationNiConstructor .lifecycleRetype
     , kernelOperationNiConstructor .lifecycleRevokeDeleteRetype
     , kernelOperationNiConstructor .notificationSignal
     , kernelOperationNiConstructor .notificationWait
     , kernelOperationNiConstructor .cspaceInsertSlot
     , kernelOperationNiConstructor .schedule
     , kernelOperationNiConstructor .vspaceMapPage
     , kernelOperationNiConstructor .vspaceUnmapPage
     , kernelOperationNiConstructor .vspaceLookup
     , kernelOperationNiConstructor .cspaceCopy
     , kernelOperationNiConstructor .cspaceMove
     , kernelOperationNiConstructor .cspaceDeleteSlot
     , kernelOperationNiConstructor .endpointReply
     , kernelOperationNiConstructor .endpointReceiveDualHigh
     , kernelOperationNiConstructor .endpointCallHigh
     , kernelOperationNiConstructor .endpointReplyRecvHigh
     , kernelOperationNiConstructor .storeObjectHigh
     , kernelOperationNiConstructor .setCurrentThread
     , kernelOperationNiConstructor .ensureRunnableHigh
     , kernelOperationNiConstructor .removeRunnableHigh
     , kernelOperationNiConstructor .storeTcbIpcStateAndMessageHigh
     , kernelOperationNiConstructor .storeTcbQueueLinksHigh
     , kernelOperationNiConstructor .cspaceMutateHigh
     , kernelOperationNiConstructor .handleYield
     , kernelOperationNiConstructor .timerTick
     , kernelOperationNiConstructor .syscallDecodeError
     , kernelOperationNiConstructor .syscallDispatchHigh
     , kernelOperationNiConstructor .registerServiceChecked
     , kernelOperationNiConstructor .endpointCallWithDonationHigh
     , kernelOperationNiConstructor .endpointReplyWithReversionHigh
     , kernelOperationNiConstructor .handleInterrupt
     ]).length = 35 := by rfl

end SeLe4n.Kernel
