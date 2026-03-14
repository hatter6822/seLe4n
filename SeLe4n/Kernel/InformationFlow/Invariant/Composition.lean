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
  | endpointSendDual
      (eid : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
      (hEndpointHigh : objectObservable ctx observer eid = false)
      (hSenderHigh : threadObservable ctx observer sender = false)
      (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
      (hCoherent : ∀ tid : SeLe4n.ThreadId,
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hStep : endpointSendDual eid sender msg st = .ok ((), st'))
      (hProjection : projectState ctx observer st' = projectState ctx observer st)
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
  | serviceStart
      (sid : ServiceId) (policy : ServicePolicy)
      (hSvcHigh : serviceObservable ctx observer sid = false)
      (hStep : SeLe4n.Kernel.serviceStart sid policy st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | serviceStop
      (sid : ServiceId) (policy : ServicePolicy)
      (hSvcHigh : serviceObservable ctx observer sid = false)
      (hStep : SeLe4n.Kernel.serviceStop sid policy st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | serviceRestart
      (sid : ServiceId) (policyStop policyStart : ServicePolicy)
      (hSvcHigh : serviceObservable ctx observer sid = false)
      (hStep : SeLe4n.Kernel.serviceRestart sid policyStop policyStart st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | schedule
      (hCurrentHigh : ∀ t, st.scheduler.current = some t →
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
      (hProj : projectState ctx observer st' = projectState ctx observer st)
      (hStep : endpointReceiveDual endpointId receiver st = .ok (sender, st'))
    : NonInterferenceStep ctx observer st st'
  | endpointCallHigh
      (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
      (hProj : projectState ctx observer st' = projectState ctx observer st)
      (hStep : endpointCall endpointId caller msg st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | endpointReplyRecvHigh
      (endpointId : SeLe4n.ObjId) (replierReceiver replyTarget : SeLe4n.ThreadId)
      (replyMsg : IpcMessage)
      (hProj : projectState ctx observer st' = projectState ctx observer st)
      (hStep : endpointReplyRecv endpointId replierReceiver replyTarget replyMsg st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | storeObjectHigh
      (oid : SeLe4n.ObjId) (obj : KernelObject)
      (hOidHigh : objectObservable ctx observer oid = false)
      (hStep : storeObject oid obj st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | setCurrentThread
      (tid : Option SeLe4n.ThreadId)
      (hTidHigh : ∀ t, tid = some t → threadObservable ctx observer t = false)
      (hCurrentHigh : ∀ t, st.scheduler.current = some t →
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
      (hCurrentHigh : ∀ t, st.scheduler.current = some t →
          threadObservable ctx observer t = false)
      (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
          threadObservable ctx observer tid = false)
      (hStep : SeLe4n.Kernel.handleYield st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | timerTick
      (hCurrentHigh : ∀ t, st.scheduler.current = some t →
          threadObservable ctx observer t = false)
      (hCurrentObjHigh : ∀ t, st.scheduler.current = some t →
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
      (hCurrentHigh : ∀ t, st.scheduler.current = some t →
          threadObservable ctx observer t = false)
      (hProj : projectState ctx observer st' = projectState ctx observer st)
    : NonInterferenceStep ctx observer st st'

/-- WS-F3/H-05/H-09: A single non-interference step preserves the observer's
projection (one-sided version). -/
theorem step_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hStep : NonInterferenceStep ctx observer st st') :
    projectState ctx observer st' = projectState ctx observer st := by
  cases hStep with
  | chooseThread next hOp =>
    have := chooseThread_preserves_state st st' next hOp; subst this; rfl
  | endpointSendDual _ _ _ _ _ _ _ _ hProj => exact hProj
  | cspaceMint src dst rights badge hSrcH hDstH hOp =>
    rcases cspaceMint_child_attenuates st st' src dst rights badge hOp with
      ⟨parent, child, hLookup, _, _⟩
    unfold cspaceMint at hOp; rw [hLookup] at hOp
    cases hMint : mintDerivedCap parent rights badge with
    | error e => simp [hMint] at hOp
    | ok c =>
      have hInsert : cspaceInsertSlot dst c st = .ok ((), st') := by simpa [hMint] using hOp
      simp only [projectState]; congr 1
      · funext oid; by_cases hObs : objectObservable ctx observer oid
        · simp [projectObjects, hObs]
          by_cases hEq : oid = dst.cnode
          · subst hEq; simp [hDstH] at hObs
          · exact congrArg (Option.map (projectKernelObject ctx observer))
              (cspaceInsertSlot_preserves_objects_ne st st' dst c oid hEq hInsert)
        · simp [projectObjects, hObs]
      · simp [projectRunnable, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · simp [projectCurrent, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · funext sid
        simp only [projectServiceStatus, lookupService,
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
  | cspaceRevoke addr hAddrH hOp =>
    unfold cspaceRevoke at hOp
    cases hL : cspaceLookupSlot addr st with
    | error e => simp [hL] at hOp
    | ok p =>
      rcases p with ⟨par, stL⟩
      have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL addr par hL
      subst stL
      cases hC : st.objects[addr.cnode]? with
      | none => simp [hL, hC] at hOp
      | some obj =>
        cases obj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hL, hC] at hOp
        | cnode cn =>
          simp [hL, hC, storeObject] at hOp; cases hOp
          rw [clearCapabilityRefsState_preserves_projectState]
          simp only [projectState]; congr 1
          · funext oid; by_cases hObs : objectObservable ctx observer oid
            · simp [projectObjects, hObs]
              have hNe : oid ≠ addr.cnode := by
                intro hEq; subst hEq; simp [hAddrH] at hObs
              simp [HashMap_getElem?_insert, Ne.symm hNe]
            · simp [projectObjects, hObs]
          · simp only [projectObjectIndex]
            split
            · rfl
            · rw [List.filter_cons]; simp [hAddrH]
  | lifecycleRetype authority target newObj hTH hOp =>
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hOp with
      ⟨_, _, _, _, _, _, hStore⟩
    exact storeObject_preserves_projection ctx observer st st' target newObj hTH hStore
  | notificationSignal ntfnId badge hNH hCo hWD hOp =>
    exact notificationSignal_projection_preserved ctx observer ntfnId badge st st'
      hNH hCo hWD hOp
  | notificationWait ntfnId waiter result hNH hWH hWOH hOp =>
    exact notificationWait_projection_preserved ctx observer ntfnId waiter result st st'
      hNH hWH hWOH hOp
  | cspaceInsertSlot dst cap hDH hOp =>
    simp only [projectState]; congr 1
    · funext oid; by_cases hObs : objectObservable ctx observer oid
      · simp [projectObjects, hObs]
        have hNe : oid ≠ dst.cnode := by intro hEq; subst hEq; simp [hDH] at hObs
        exact congrArg (Option.map (projectKernelObject ctx observer))
          (cspaceInsertSlot_preserves_objects_ne st st' dst cap oid hNe hOp)
      · simp [projectObjects, hObs]
    · simp [projectRunnable, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · simp [projectCurrent, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · funext sid; simp only [projectServiceStatus, lookupService,
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
  | serviceStart sid policy hSH hOp =>
    simp only [projectState]; congr 1
    · funext oid; simp only [projectObjects]
      by_cases hObs : objectObservable ctx observer oid
      · simp [hObs]; rw [serviceStart_preserves_objects st st' sid policy hOp]
      · simp [hObs]
    · simp [projectRunnable, serviceStart_preserves_scheduler st st' sid policy hOp]
    · simp [projectCurrent, serviceStart_preserves_scheduler st st' sid policy hOp]
    · funext s; simp only [projectServiceStatus]
      by_cases hObs : serviceObservable ctx observer s
      · simp [hObs]; by_cases hEq : s = sid
        · subst hEq; simp [hSH] at hObs
        · rw [serviceStart_preserves_lookupService_ne st st' sid policy s hEq hOp]
      · simp [hObs]
    · simp [projectActiveDomain, serviceStart_preserves_scheduler st st' sid policy hOp]
    · funext irq; simp only [projectIrqHandlers]
      rw [serviceStart_preserves_irqHandlers st st' sid policy hOp]
    · simp only [projectObjectIndex]
      rw [serviceStart_preserves_objectIndex st st' sid policy hOp]
    · simp [projectDomainTimeRemaining, serviceStart_preserves_scheduler st st' sid policy hOp]
    · simp [projectDomainSchedule, serviceStart_preserves_scheduler st st' sid policy hOp]
    · simp [projectDomainScheduleIndex, serviceStart_preserves_scheduler st st' sid policy hOp]
    · simp [projectMachineRegs, serviceStart_preserves_scheduler st st' sid policy hOp,
            serviceStart_preserves_machine st st' sid policy hOp]
  | serviceStop sid policy hSH hOp =>
    simp only [projectState]; congr 1
    · funext oid; simp only [projectObjects]
      by_cases hObs : objectObservable ctx observer oid
      · simp [hObs]; rw [serviceStop_preserves_objects st st' sid policy hOp]
      · simp [hObs]
    · simp [projectRunnable, serviceStop_preserves_scheduler st st' sid policy hOp]
    · simp [projectCurrent, serviceStop_preserves_scheduler st st' sid policy hOp]
    · funext s; simp only [projectServiceStatus]
      by_cases hObs : serviceObservable ctx observer s
      · simp [hObs]; by_cases hEq : s = sid
        · subst hEq; simp [hSH] at hObs
        · rw [serviceStop_preserves_lookupService_ne st st' sid policy s hEq hOp]
      · simp [hObs]
    · simp [projectActiveDomain, serviceStop_preserves_scheduler st st' sid policy hOp]
    · funext irq; simp only [projectIrqHandlers]
      rw [serviceStop_preserves_irqHandlers st st' sid policy hOp]
    · simp only [projectObjectIndex]
      rw [serviceStop_preserves_objectIndex st st' sid policy hOp]
    · simp [projectDomainTimeRemaining, serviceStop_preserves_scheduler st st' sid policy hOp]
    · simp [projectDomainSchedule, serviceStop_preserves_scheduler st st' sid policy hOp]
    · simp [projectDomainScheduleIndex, serviceStop_preserves_scheduler st st' sid policy hOp]
    · simp [projectMachineRegs, serviceStop_preserves_scheduler st st' sid policy hOp,
            serviceStop_preserves_machine st st' sid policy hOp]
  | serviceRestart sid policyStop policyStart hSH hOp =>
    rcases serviceRestart_decompose st st' sid policyStop policyStart hOp with ⟨mid, hStop, hStart⟩
    have hMid : projectState ctx observer mid = projectState ctx observer st := by
      simp only [projectState]; congr 1
      · funext oid; simp only [projectObjects]
        by_cases hObs : objectObservable ctx observer oid
        · simp [hObs]; rw [serviceStop_preserves_objects st mid sid policyStop hStop]
        · simp [hObs]
      · simp [projectRunnable, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · simp [projectCurrent, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · funext s; simp only [projectServiceStatus]
        by_cases hObs : serviceObservable ctx observer s
        · simp [hObs]; by_cases hEq : s = sid
          · subst hEq; simp [hSH] at hObs
          · rw [serviceStop_preserves_lookupService_ne st mid sid policyStop s hEq hStop]
        · simp [hObs]
      · simp [projectActiveDomain, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · funext irq; simp only [projectIrqHandlers]
        rw [serviceStop_preserves_irqHandlers st mid sid policyStop hStop]
      · simp only [projectObjectIndex]
        rw [serviceStop_preserves_objectIndex st mid sid policyStop hStop]
      · simp [projectDomainTimeRemaining, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · simp [projectDomainSchedule, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · simp [projectDomainScheduleIndex, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · simp [projectMachineRegs, serviceStop_preserves_scheduler st mid sid policyStop hStop,
              serviceStop_preserves_machine st mid sid policyStop hStop]
    have hFinal : projectState ctx observer st' = projectState ctx observer mid := by
      simp only [projectState]; congr 1
      · funext oid; simp only [projectObjects]
        by_cases hObs : objectObservable ctx observer oid
        · simp [hObs]; rw [serviceStart_preserves_objects mid st' sid policyStart hStart]
        · simp [hObs]
      · simp [projectRunnable, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · simp [projectCurrent, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · funext s; simp only [projectServiceStatus]
        by_cases hObs : serviceObservable ctx observer s
        · simp [hObs]; by_cases hEq : s = sid
          · subst hEq; simp [hSH] at hObs
          · rw [serviceStart_preserves_lookupService_ne mid st' sid policyStart s hEq hStart]
        · simp [hObs]
      · simp [projectActiveDomain, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · funext irq; simp only [projectIrqHandlers]
        rw [serviceStart_preserves_irqHandlers mid st' sid policyStart hStart]
      · simp only [projectObjectIndex]
        rw [serviceStart_preserves_objectIndex mid st' sid policyStart hStart]
      · simp [projectDomainTimeRemaining, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · simp [projectDomainSchedule, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · simp [projectDomainScheduleIndex, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · simp [projectMachineRegs, serviceStart_preserves_scheduler mid st' sid policyStart hStart,
              serviceStart_preserves_machine mid st' sid policyStart hStart]
    rw [hFinal, hMid]
  | schedule hCurH hAllR hOp =>
    exact schedule_preserves_projection ctx observer st st' hCurH hAllR hOp
  | vspaceMapPage asid vaddr paddr hRH hOp =>
    exact vspaceMapPage_preserves_projection ctx observer asid vaddr paddr st st' hRH hOp
  | vspaceUnmapPage asid vaddr hRH hOp =>
    exact vspaceUnmapPage_preserves_projection ctx observer asid vaddr st st' hRH hOp
  | vspaceLookup asid vaddr paddr hOp =>
    have := vspaceLookup_preserves_state st asid vaddr paddr st' hOp; subst this; rfl
  | cspaceCopy src dst hSH hDH hOp =>
    exact cspaceCopy_preserves_projection ctx observer src dst st st' hSH hDH hOp
  | cspaceMove src dst hSH hDH hOp =>
    exact cspaceMove_preserves_projection ctx observer src dst st st' hSH hDH hOp
  | cspaceDeleteSlot addr hAH hOp =>
    exact cspaceDeleteSlot_preserves_projection ctx observer addr st st' hAH hOp
  | endpointReply replier target msg hTH hTOH hOp =>
    exact endpointReply_preserves_projection ctx observer replier target msg st st' hTH hTOH hOp
  | endpointReceiveDualHigh _ _ _ hProj _ => exact hProj
  | endpointCallHigh _ _ _ hProj _ => exact hProj
  | endpointReplyRecvHigh _ _ _ _ hProj _ => exact hProj
  | storeObjectHigh oid obj hOH hOp =>
    exact storeObject_preserves_projection ctx observer st st' oid obj hOH hOp
  | setCurrentThread tid hTidH hCurH hOp =>
    exact setCurrentThread_preserves_projection ctx observer tid st st' hTidH hCurH hOp
  | ensureRunnableHigh tid hTH hEq =>
    rw [hEq]; exact ensureRunnable_preserves_projection ctx observer st tid hTH
  | removeRunnableHigh tid hTH hEq =>
    rw [hEq]; exact removeRunnable_preserves_projection ctx observer st tid hTH
  | storeTcbIpcStateAndMessageHigh tid ipc msg hTOH hOp =>
    exact storeTcbIpcStateAndMessage_preserves_projection ctx observer st st' tid ipc msg hTOH hOp
  | storeTcbQueueLinksHigh tid prev pprev next hTOH hOp =>
    exact storeTcbQueueLinks_preserves_projection ctx observer st st' tid prev pprev next hTOH hOp
  | cspaceMutateHigh addr rights badge hAH hOp =>
    unfold cspaceMutate at hOp
    cases hL : cspaceLookupSlot addr st with
    | error e => simp [hL] at hOp
    | ok p =>
      rcases p with ⟨cap, stL⟩
      have hStEq := cspaceLookupSlot_preserves_state st stL addr cap hL
      subst stL
      simp only [hL] at hOp
      split at hOp
      · -- rights subset: storeObject + storeCapabilityRef
        split at hOp
        · -- some (.cnode cn)
          next cn =>
          split at hOp
          · -- storeObject error
            next e hStore => simp at hOp
          · -- storeObject ok
            next stMid hStore =>
            have hProjMid := storeObject_preserves_projection ctx observer st stMid
                addr.cnode _ hAH hStore
            have hProjFinal := storeCapabilityRef_preserves_projection ctx observer stMid st'
                addr (some _) hOp
            rw [hProjFinal, hProjMid]
        · -- not a cnode
          simp at hOp
      · -- rights not subset: error
        simp at hOp
  | handleYield hCH hAR hOp =>
    exact handleYield_preserves_projection ctx observer st st' hCH hAR hOp
  | timerTick hCH hCOH hAR hOp =>
    exact timerTick_preserves_projection ctx observer st st' hCH hCOH hAR hOp
  | syscallDecodeError hEq => subst hEq; rfl
  | syscallDispatchHigh _ hProj => exact hProj

/-- WS-F3/H-05/H-09: Primary IF-M4 composition theorem — single-step bundle
non-interference. -/
theorem composedNonInterference_step
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : NonInterferenceStep ctx observer s₁ s₁')
    (hStep₂ : NonInterferenceStep ctx observer s₂ s₂') :
    lowEquivalent ctx observer s₁' s₂' := by
  have h₁ := step_preserves_projection ctx observer s₁ s₁' hStep₁
  have h₂ := step_preserves_projection ctx observer s₂ s₂' hStep₂
  unfold lowEquivalent; rw [h₁, h₂]; exact hLow

/-- WS-F3/H-05: Multi-step trace of non-interference steps. -/
inductive NonInterferenceTrace
    (ctx : LabelingContext) (observer : IfObserver) :
    SystemState → SystemState → Prop where
  | nil (st : SystemState) : NonInterferenceTrace ctx observer st st
  | cons (st₁ st₂ st₃ : SystemState)
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
  | cons _ st₂ _ hStep _ ih =>
    rw [ih, step_preserves_projection ctx observer _ st₂ hStep]

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
-- Preservation framework (composition helper)
-- ============================================================================

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
    ctx observer targetId obj₁ obj₂ s₁ s₂ s₁' s₂' hLow hTargetHigh hStore₁ hStore₂

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

end SeLe4n.Kernel
