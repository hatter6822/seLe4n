/-!
# Information-Flow Invariant Surface (WS-D2, F-05)

This module contains non-interference preservation theorems for kernel operations.

**IF-M1 seed theorem:** `endpointSend_preserves_lowEquivalent` (original)

**WS-D2 extensions:**
- `chooseThread_preserves_lowEquivalent` — scheduler read-only operation
- `cspaceMint_preserves_lowEquivalent` — capability authority transfer
- `lifecycleRetypeObject_preserves_lowEquivalent` — object lifecycle transition
- `serviceRestart_preserves_lowEquivalent` — service orchestration

Each theorem states: if two states are low-equivalent for an observer, and an operation
on a high-domain entity succeeds on both states, then the resulting states remain
low-equivalent. This is the classic unwinding condition for noninterference.
-/
import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Lifecycle.Operations
import SeLe4n.Kernel.Service.Operations

namespace SeLe4n.Kernel

open SeLe4n.Model

/-! ## IF-M1 seed: endpoint send noninterference -/

/-- A successful endpoint send preserves low-equivalence for observers that cannot
see the sender thread and cannot observe the endpoint object itself. -/
theorem endpointSend_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (_hSenderHigh : threadObservable ctx observer sender = false)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hStep₁ : endpointSend endpointId sender s₁ = .ok ((), s₁'))
    (hStep₂ : endpointSend endpointId sender s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  rcases endpointSend_ok_as_storeObject s₁ s₁' endpointId sender hStep₁ with ⟨ep₁, hStore₁⟩
  rcases endpointSend_ok_as_storeObject s₂ s₂' endpointId sender hStep₂ with ⟨ep₂, hStore₂⟩
  have hObjLow : projectObjects ctx observer s₁ = projectObjects ctx observer s₂ := by
    exact congrArg ObservableState.objects hLow
  have hRunLow : projectRunnable ctx observer s₁ = projectRunnable ctx observer s₂ := by
    exact congrArg ObservableState.runnable hLow
  have hCurLow : projectCurrent ctx observer s₁ = projectCurrent ctx observer s₂ := by
    exact congrArg ObservableState.current hLow
  have hSvcLow : projectServiceStatus ctx observer s₁ = projectServiceStatus ctx observer s₂ := by
    exact congrArg ObservableState.services hLow
  have hObj' : projectObjects ctx observer s₁' = projectObjects ctx observer s₂' := by
    funext oid
    by_cases hObs : objectObservable ctx observer oid
    · by_cases hEq : oid = endpointId
      · subst hEq
        simp [projectObjects, hEndpointHigh]
      · have hObj₁ : s₁'.objects oid = s₁.objects oid :=
          storeObject_objects_ne s₁ s₁' endpointId oid (.endpoint ep₁) hEq hStore₁
        have hObj₂ : s₂'.objects oid = s₂.objects oid :=
          storeObject_objects_ne s₂ s₂' endpointId oid (.endpoint ep₂) hEq hStore₂
        have hObjBase : s₁.objects oid = s₂.objects oid := by
          have hBase := congrFun hObjLow oid
          simpa [projectObjects, hObs] using hBase
        simpa [projectObjects, hObs, hObj₁, hObj₂] using hObjBase
    · simp [projectObjects, hObs]
  have hRun' : projectRunnable ctx observer s₁' = projectRunnable ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' endpointId (.endpoint ep₁) hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' endpointId (.endpoint ep₂) hStore₂
    simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
  have hCur' : projectCurrent ctx observer s₁' = projectCurrent ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' endpointId (.endpoint ep₁) hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' endpointId (.endpoint ep₂) hStore₂
    simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
  have hSvc' : projectServiceStatus ctx observer s₁' = projectServiceStatus ctx observer s₂' := by
    unfold storeObject at hStore₁ hStore₂
    cases hStore₁
    cases hStore₂
    simpa [projectServiceStatus] using hSvcLow
  unfold lowEquivalent
  simp [projectState, hObj', hRun', hCur', hSvc']

/-! ## WS-D2 state-property helpers -/

/-- `storeObject` preserves the services field (only objects, objectIndex, lifecycle change). -/
private theorem storeObject_services_eq
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.services = st.services := by
  unfold storeObject at hStore
  cases hStore
  rfl

/-- `storeCapabilityRef` preserves the scheduler (only lifecycle changes). -/
private theorem storeCapabilityRef_scheduler_eq
    (st st' : SystemState) (ref : SlotRef) (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeCapabilityRef at hStep
  simp at hStep
  cases hStep
  rfl

/-- `storeCapabilityRef` preserves the services (only lifecycle changes). -/
private theorem storeCapabilityRef_services_eq
    (st st' : SystemState) (ref : SlotRef) (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.services = st.services := by
  unfold storeCapabilityRef at hStep
  simp at hStep
  cases hStep
  rfl

/-! ## WS-D2 cspaceInsertSlot state-property helpers -/

/-- Decompose a successful `cspaceInsertSlot` into its constituent state transitions. -/
private theorem cspaceInsertSlot_ok_decompose
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    ∃ cn stMid,
      st.objects addr.cnode = some (.cnode cn) ∧
      storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st = .ok ((), stMid) ∧
      storeCapabilityRef addr (some cap.target) stMid = .ok ((), st') := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects addr.cnode with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | cnode cn =>
          simp [hObj] at hStep
          cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
          | error e => simp [hStore] at hStep
          | ok pair =>
              rcases pair with ⟨_, stMid⟩
              exact ⟨cn, stMid, rfl, hStore, by simpa [hStore] using hStep⟩
      | tcb _ => simp [hObj] at hStep
      | endpoint _ => simp [hObj] at hStep
      | notification _ => simp [hObj] at hStep
      | vspaceRoot _ => simp [hObj] at hStep

/-- `cspaceInsertSlot` preserves objects at IDs other than the target CNode. -/
private theorem cspaceInsertSlot_ok_objects_ne
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ addr.cnode)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  rcases cspaceInsertSlot_ok_decompose st st' addr cap hStep with ⟨_, stMid, _, hStore, hRef⟩
  have h1 : stMid.objects oid = st.objects oid :=
    SeLe4n.Model.storeObject_objects_ne st stMid addr.cnode oid _ hNe hStore
  have h2 : st'.objects = stMid.objects :=
    SeLe4n.Model.storeCapabilityRef_preserves_objects stMid st' addr _ hRef
  rw [congrFun h2 oid, h1]

/-- `cspaceInsertSlot` preserves the scheduler. -/
private theorem cspaceInsertSlot_ok_scheduler_eq
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  rcases cspaceInsertSlot_ok_decompose st st' addr cap hStep with ⟨_, stMid, _, hStore, hRef⟩
  have h1 : stMid.scheduler = st.scheduler :=
    SeLe4n.Model.storeObject_scheduler_eq st stMid addr.cnode _ hStore
  have h2 : st'.scheduler = stMid.scheduler :=
    storeCapabilityRef_scheduler_eq stMid st' addr _ hRef
  rw [h2, h1]

/-- `cspaceInsertSlot` preserves services. -/
private theorem cspaceInsertSlot_ok_services_eq
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.services = st.services := by
  rcases cspaceInsertSlot_ok_decompose st st' addr cap hStep with ⟨_, stMid, _, hStore, hRef⟩
  have h1 : stMid.services = st.services :=
    storeObject_services_eq st stMid addr.cnode _ hStore
  have h2 : st'.services = stMid.services :=
    storeCapabilityRef_services_eq stMid st' addr _ hRef
  rw [h2, h1]

/-! ## WS-D2 cspaceMint decomposition -/

/-- Decompose a successful `cspaceMint` into lookup + mint + insert, with state preserved
through the lookup step. -/
private theorem cspaceMint_ok_as_insertSlot
    (st st' : SystemState) (src dst : CSpaceAddr)
    (rights : List AccessRight) (badge : Option SeLe4n.Badge)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    ∃ child, cspaceInsertSlot dst child st = .ok ((), st') := by
  unfold cspaceMint at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_ok_state_eq st src parent st1 hSrc
      subst hSt1
      cases hMint : mintDerivedCap parent rights badge with
      | error e => simp [hSrc, hMint] at hStep
      | ok child =>
          exact ⟨child, by simpa [hSrc, hMint] using hStep⟩

/-! ## WS-D2 service operation state-property helpers -/

/-- A successful `serviceStop` preserves objects (only services change). -/
private theorem serviceStop_ok_objects_eq
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStop sid policy st = .ok ((), st')) :
    st'.objects = st.objects := by
  unfold serviceStop at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      by_cases hRunning : svc.status = .running
      · by_cases hPolicy : policy svc
        · unfold storeServiceEntry at hStep
          simp [hLookup, hRunning, hPolicy, storeServiceState] at hStep
          cases hStep
          rfl
        · simp [hLookup, hRunning, hPolicy] at hStep
      · simp [hLookup, hRunning] at hStep

/-- A successful `serviceStop` preserves scheduler (only services change). -/
private theorem serviceStop_ok_scheduler_eq
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStop sid policy st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold serviceStop at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      by_cases hRunning : svc.status = .running
      · by_cases hPolicy : policy svc
        · unfold storeServiceEntry at hStep
          simp [hLookup, hRunning, hPolicy, storeServiceState] at hStep
          cases hStep
          rfl
        · simp [hLookup, hRunning, hPolicy] at hStep
      · simp [hLookup, hRunning] at hStep

/-- A successful `serviceStop` preserves services at other IDs. -/
private theorem serviceStop_ok_services_ne
    (st st' : SystemState) (sid sid' : ServiceId) (policy : ServicePolicy)
    (hNe : sid' ≠ sid)
    (hStep : serviceStop sid policy st = .ok ((), st')) :
    st'.services sid' = st.services sid' := by
  unfold serviceStop at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      by_cases hRunning : svc.status = .running
      · by_cases hPolicy : policy svc
        · unfold storeServiceEntry at hStep
          simp [hLookup, hRunning, hPolicy, storeServiceState] at hStep
          cases hStep
          simp [hNe]
        · simp [hLookup, hRunning, hPolicy] at hStep
      · simp [hLookup, hRunning] at hStep

/-- A successful `serviceStart` preserves objects (only services change). -/
private theorem serviceStart_ok_objects_eq
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStart sid policy st = .ok ((), st')) :
    st'.objects = st.objects := by
  unfold serviceStart at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      by_cases hStopped : svc.status = .stopped
      · by_cases hPolicy : policy svc
        · by_cases hDeps : dependenciesSatisfied st sid
          · unfold storeServiceEntry at hStep
            simp [hLookup, hStopped, hPolicy, hDeps, storeServiceState] at hStep
            cases hStep
            rfl
          · simp [hLookup, hStopped, hPolicy, hDeps] at hStep
        · simp [hLookup, hStopped, hPolicy] at hStep
      · simp [hLookup, hStopped] at hStep

/-- A successful `serviceStart` preserves scheduler (only services change). -/
private theorem serviceStart_ok_scheduler_eq
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStart sid policy st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold serviceStart at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      by_cases hStopped : svc.status = .stopped
      · by_cases hPolicy : policy svc
        · by_cases hDeps : dependenciesSatisfied st sid
          · unfold storeServiceEntry at hStep
            simp [hLookup, hStopped, hPolicy, hDeps, storeServiceState] at hStep
            cases hStep
            rfl
          · simp [hLookup, hStopped, hPolicy, hDeps] at hStep
        · simp [hLookup, hStopped, hPolicy] at hStep
      · simp [hLookup, hStopped] at hStep

/-- A successful `serviceStart` preserves services at other IDs. -/
private theorem serviceStart_ok_services_ne
    (st st' : SystemState) (sid sid' : ServiceId) (policy : ServicePolicy)
    (hNe : sid' ≠ sid)
    (hStep : serviceStart sid policy st = .ok ((), st')) :
    st'.services sid' = st.services sid' := by
  unfold serviceStart at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      by_cases hStopped : svc.status = .stopped
      · by_cases hPolicy : policy svc
        · by_cases hDeps : dependenciesSatisfied st sid
          · unfold storeServiceEntry at hStep
            simp [hLookup, hStopped, hPolicy, hDeps, storeServiceState] at hStep
            cases hStep
            simp [hNe]
          · simp [hLookup, hStopped, hPolicy, hDeps] at hStep
        · simp [hLookup, hStopped, hPolicy] at hStep
      · simp [hLookup, hStopped] at hStep

/-! ## WS-D2 noninterference: storeObject-based generic unwinding -/

/-- Generic noninterference unwinding lemma for operations that reduce to a single `storeObject`
at a high-domain object ID. This captures the common proof skeleton shared by `endpointSend`,
`lifecycleRetypeObject`, and similar store-based operations. -/
private theorem storeObject_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (targetId : SeLe4n.ObjId)
    (obj₁ obj₂ : KernelObject)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hTargetHigh : objectObservable ctx observer targetId = false)
    (hStore₁ : storeObject targetId obj₁ s₁ = .ok ((), s₁'))
    (hStore₂ : storeObject targetId obj₂ s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hObjLow : projectObjects ctx observer s₁ = projectObjects ctx observer s₂ :=
    congrArg ObservableState.objects hLow
  have hRunLow : projectRunnable ctx observer s₁ = projectRunnable ctx observer s₂ :=
    congrArg ObservableState.runnable hLow
  have hCurLow : projectCurrent ctx observer s₁ = projectCurrent ctx observer s₂ :=
    congrArg ObservableState.current hLow
  have hSvcLow : projectServiceStatus ctx observer s₁ = projectServiceStatus ctx observer s₂ :=
    congrArg ObservableState.services hLow
  have hObj' : projectObjects ctx observer s₁' = projectObjects ctx observer s₂' := by
    funext oid
    by_cases hObs : objectObservable ctx observer oid
    · by_cases hEq : oid = targetId
      · subst hEq; simp [projectObjects, hTargetHigh]
      · have hObj₁ : s₁'.objects oid = s₁.objects oid :=
          SeLe4n.Model.storeObject_objects_ne s₁ s₁' targetId oid obj₁ hEq hStore₁
        have hObj₂ : s₂'.objects oid = s₂.objects oid :=
          SeLe4n.Model.storeObject_objects_ne s₂ s₂' targetId oid obj₂ hEq hStore₂
        have hObjBase : s₁.objects oid = s₂.objects oid := by
          have hBase := congrFun hObjLow oid
          simpa [projectObjects, hObs] using hBase
        simpa [projectObjects, hObs, hObj₁, hObj₂] using hObjBase
    · simp [projectObjects, hObs]
  have hRun' : projectRunnable ctx observer s₁' = projectRunnable ctx observer s₂' := by
    have hSched₁ := SeLe4n.Model.storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := SeLe4n.Model.storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
  have hCur' : projectCurrent ctx observer s₁' = projectCurrent ctx observer s₂' := by
    have hSched₁ := SeLe4n.Model.storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := SeLe4n.Model.storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
  have hSvc' : projectServiceStatus ctx observer s₁' = projectServiceStatus ctx observer s₂' := by
    unfold storeObject at hStore₁ hStore₂
    cases hStore₁; cases hStore₂
    simpa [projectServiceStatus] using hSvcLow
  unfold lowEquivalent
  simp [projectState, hObj', hRun', hCur', hSvc']

/-! ## WS-D2 noninterference theorem 1: chooseThread -/

/-- A successful `chooseThread` preserves low-equivalence.

`chooseThread` is a read-only operation that does not modify state, so this
follows trivially from `chooseThread_preserves_state`. -/
theorem chooseThread_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (next₁ : Option SeLe4n.ThreadId)
    (next₂ : Option SeLe4n.ThreadId)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : chooseThread s₁ = .ok (next₁, s₁'))
    (hStep₂ : chooseThread s₂ = .ok (next₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have h₁ : s₁' = s₁ := chooseThread_preserves_state s₁ s₁' next₁ hStep₁
  have h₂ : s₂' = s₂ := chooseThread_preserves_state s₂ s₂' next₂ hStep₂
  subst h₁; subst h₂
  exact hLow

/-! ## WS-D2 noninterference theorem 2: cspaceMint -/

/-- A successful `cspaceMint` preserves low-equivalence for observers that cannot observe
the destination CNode. The destination CNode is the only object modified by the mint
operation. -/
theorem cspaceMint_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep₁ : cspaceMint src dst rights badge s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceMint src dst rights badge s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  rcases cspaceMint_ok_as_insertSlot s₁ s₁' src dst rights badge hStep₁ with ⟨child₁, hInsert₁⟩
  rcases cspaceMint_ok_as_insertSlot s₂ s₂' src dst rights badge hStep₂ with ⟨child₂, hInsert₂⟩
  have hObjLow : projectObjects ctx observer s₁ = projectObjects ctx observer s₂ :=
    congrArg ObservableState.objects hLow
  have hRunLow : projectRunnable ctx observer s₁ = projectRunnable ctx observer s₂ :=
    congrArg ObservableState.runnable hLow
  have hCurLow : projectCurrent ctx observer s₁ = projectCurrent ctx observer s₂ :=
    congrArg ObservableState.current hLow
  have hSvcLow : projectServiceStatus ctx observer s₁ = projectServiceStatus ctx observer s₂ :=
    congrArg ObservableState.services hLow
  have hObj' : projectObjects ctx observer s₁' = projectObjects ctx observer s₂' := by
    funext oid
    by_cases hObs : objectObservable ctx observer oid
    · by_cases hEq : oid = dst.cnode
      · subst hEq; simp [projectObjects, hDstHigh]
      · have hObj₁ : s₁'.objects oid = s₁.objects oid :=
          cspaceInsertSlot_ok_objects_ne s₁ s₁' dst child₁ oid hEq hInsert₁
        have hObj₂ : s₂'.objects oid = s₂.objects oid :=
          cspaceInsertSlot_ok_objects_ne s₂ s₂' dst child₂ oid hEq hInsert₂
        have hObjBase : s₁.objects oid = s₂.objects oid := by
          have hBase := congrFun hObjLow oid
          simpa [projectObjects, hObs] using hBase
        simpa [projectObjects, hObs, hObj₁, hObj₂] using hObjBase
    · simp [projectObjects, hObs]
  have hRun' : projectRunnable ctx observer s₁' = projectRunnable ctx observer s₂' := by
    have hSched₁ := cspaceInsertSlot_ok_scheduler_eq s₁ s₁' dst child₁ hInsert₁
    have hSched₂ := cspaceInsertSlot_ok_scheduler_eq s₂ s₂' dst child₂ hInsert₂
    simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
  have hCur' : projectCurrent ctx observer s₁' = projectCurrent ctx observer s₂' := by
    have hSched₁ := cspaceInsertSlot_ok_scheduler_eq s₁ s₁' dst child₁ hInsert₁
    have hSched₂ := cspaceInsertSlot_ok_scheduler_eq s₂ s₂' dst child₂ hInsert₂
    simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
  have hSvc' : projectServiceStatus ctx observer s₁' = projectServiceStatus ctx observer s₂' := by
    have hSvc₁ := cspaceInsertSlot_ok_services_eq s₁ s₁' dst child₁ hInsert₁
    have hSvc₂ := cspaceInsertSlot_ok_services_eq s₂ s₂' dst child₂ hInsert₂
    simpa [projectServiceStatus, hSvc₁, hSvc₂] using hSvcLow
  unfold lowEquivalent
  simp [projectState, hObj', hRun', hCur', hSvc']

/-! ## WS-D2 noninterference theorem 3: lifecycleRetypeObject -/

/-- A successful `lifecycleRetypeObject` preserves low-equivalence for observers that
cannot observe the retyped target object. The target is the only object modified. -/
theorem lifecycleRetypeObject_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hTargetHigh : objectObservable ctx observer target = false)
    (hStep₁ : lifecycleRetypeObject authority target newObj s₁ = .ok ((), s₁'))
    (hStep₂ : lifecycleRetypeObject authority target newObj s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  rcases lifecycleRetypeObject_ok_as_storeObject s₁ s₁' authority target newObj hStep₁ with
    ⟨_, _, _, _, _, _, hStore₁⟩
  rcases lifecycleRetypeObject_ok_as_storeObject s₂ s₂' authority target newObj hStep₂ with
    ⟨_, _, _, _, _, _, hStore₂⟩
  exact storeObject_preserves_lowEquivalent ctx observer target newObj newObj
    s₁ s₂ s₁' s₂' hLow hTargetHigh hStore₁ hStore₂

/-! ## WS-D2 noninterference theorem 4: serviceRestart -/

/-- A successful `serviceRestart` preserves low-equivalence for observers that cannot
observe the restarted service. Only the target service's status changes; objects and
scheduler are unaffected. -/
theorem serviceRestart_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (sid : ServiceId)
    (policyAllowsStop policyAllowsStart : ServicePolicy)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hServiceHigh : serviceObservable ctx observer sid = false)
    (hStep₁ : serviceRestart sid policyAllowsStop policyAllowsStart s₁ = .ok ((), s₁'))
    (hStep₂ : serviceRestart sid policyAllowsStop policyAllowsStart s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  rcases serviceRestart_ok_implies_staged_steps s₁ s₁' sid policyAllowsStop policyAllowsStart hStep₁ with
    ⟨sMid₁, hStop₁, hStart₁⟩
  rcases serviceRestart_ok_implies_staged_steps s₂ s₂' sid policyAllowsStop policyAllowsStart hStep₂ with
    ⟨sMid₂, hStop₂, hStart₂⟩
  have hObjLow : projectObjects ctx observer s₁ = projectObjects ctx observer s₂ :=
    congrArg ObservableState.objects hLow
  have hRunLow : projectRunnable ctx observer s₁ = projectRunnable ctx observer s₂ :=
    congrArg ObservableState.runnable hLow
  have hCurLow : projectCurrent ctx observer s₁ = projectCurrent ctx observer s₂ :=
    congrArg ObservableState.current hLow
  have hSvcLow : projectServiceStatus ctx observer s₁ = projectServiceStatus ctx observer s₂ :=
    congrArg ObservableState.services hLow
  -- Objects are preserved through both stop and start transitions
  have hObj₁ : s₁'.objects = s₁.objects := by
    have h1 := serviceStop_ok_objects_eq s₁ sMid₁ sid policyAllowsStop hStop₁
    have h2 := serviceStart_ok_objects_eq sMid₁ s₁' sid policyAllowsStart hStart₁
    rw [h2, h1]
  have hObj₂ : s₂'.objects = s₂.objects := by
    have h1 := serviceStop_ok_objects_eq s₂ sMid₂ sid policyAllowsStop hStop₂
    have h2 := serviceStart_ok_objects_eq sMid₂ s₂' sid policyAllowsStart hStart₂
    rw [h2, h1]
  -- Scheduler is preserved through both stop and start transitions
  have hSched₁ : s₁'.scheduler = s₁.scheduler := by
    have h1 := serviceStop_ok_scheduler_eq s₁ sMid₁ sid policyAllowsStop hStop₁
    have h2 := serviceStart_ok_scheduler_eq sMid₁ s₁' sid policyAllowsStart hStart₁
    rw [h2, h1]
  have hSched₂ : s₂'.scheduler = s₂.scheduler := by
    have h1 := serviceStop_ok_scheduler_eq s₂ sMid₂ sid policyAllowsStop hStop₂
    have h2 := serviceStart_ok_scheduler_eq sMid₂ s₂' sid policyAllowsStart hStart₂
    rw [h2, h1]
  have hObj' : projectObjects ctx observer s₁' = projectObjects ctx observer s₂' := by
    simpa [projectObjects, hObj₁, hObj₂] using hObjLow
  have hRun' : projectRunnable ctx observer s₁' = projectRunnable ctx observer s₂' := by
    simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
  have hCur' : projectCurrent ctx observer s₁' = projectCurrent ctx observer s₂' := by
    simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
  have hSvc' : projectServiceStatus ctx observer s₁' = projectServiceStatus ctx observer s₂' := by
    funext sid'
    by_cases hObs : serviceObservable ctx observer sid'
    · by_cases hEq : sid' = sid
      · subst hEq; simp [hObs] at hServiceHigh
      · have hSvc₁ : s₁'.services sid' = s₁.services sid' := by
          have h1 := serviceStop_ok_services_ne s₁ sMid₁ sid sid' policyAllowsStop hEq hStop₁
          have h2 := serviceStart_ok_services_ne sMid₁ s₁' sid sid' policyAllowsStart hEq hStart₁
          rw [h2, h1]
        have hSvc₂ : s₂'.services sid' = s₂.services sid' := by
          have h1 := serviceStop_ok_services_ne s₂ sMid₂ sid sid' policyAllowsStop hEq hStop₂
          have h2 := serviceStart_ok_services_ne sMid₂ s₂' sid sid' policyAllowsStart hEq hStart₂
          rw [h2, h1]
        have hSvcBase : (projectServiceStatus ctx observer s₁) sid' = (projectServiceStatus ctx observer s₂) sid' :=
          congrFun hSvcLow sid'
        simpa [projectServiceStatus, hObs, lookupService, hSvc₁, hSvc₂] using hSvcBase
    · simp [projectServiceStatus, hObs]
  unfold lowEquivalent
  simp [projectState, hObj', hRun', hCur', hSvc']

end SeLe4n.Kernel
