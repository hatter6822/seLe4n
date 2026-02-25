import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Capability.Invariant
import SeLe4n.Kernel.Scheduler.Operations
import SeLe4n.Kernel.Lifecycle.Operations

/-!
# Information-Flow Non-Interference Proofs

This module contains non-interference theorems proving that high-domain kernel
operations do not leak information to low-clearance observers.

## Proof scope qualification (F-16)

**Non-interference theorems** (critical for security assurance — prove that a
high-domain operation preserves low-equivalence for unrelated observers):
- `endpointSend_preserves_lowEquivalent`
- `chooseThread_preserves_lowEquivalent` (WS-D2 / TPI-D01)
- `cspaceMint_preserves_lowEquivalent` (WS-D2 / TPI-D02)
- `cspaceRevoke_preserves_lowEquivalent` (WS-D2 / TPI-D02)
- `lifecycleRetypeObject_preserves_lowEquivalent` (WS-D2 / TPI-D03)

**Shared proof infrastructure** (high assurance):
- `storeObject_at_unobservable_preserves_lowEquivalent` — generic proof skeleton
  for any `storeObject`-based operation at a non-observable ID.

All theorems in this module are substantive non-interference proofs. There are no
error-case preservation theorems.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- Shared non-interference proof infrastructure
-- ============================================================================

/-- A generic storeObject at a non-observable id preserves low-equivalence.
This is the shared proof skeleton used by multiple non-interference theorems. -/
theorem storeObject_at_unobservable_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
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
      · subst hEq; simp [hTargetHigh] at hObs
      · have hObj₁ : s₁'.objects oid = s₁.objects oid :=
          storeObject_objects_ne s₁ s₁' targetId oid obj₁ hEq hStore₁
        have hObj₂ : s₂'.objects oid = s₂.objects oid :=
          storeObject_objects_ne s₂ s₂' targetId oid obj₂ hEq hStore₂
        have hObjBase : s₁.objects oid = s₂.objects oid := by
          have hBase := congrFun hObjLow oid
          simpa [projectObjects, hObs] using hBase
        simpa [projectObjects, hObs, hObj₁, hObj₂] using hObjBase
    · simp [projectObjects, hObs]
  have hRun' : projectRunnable ctx observer s₁' = projectRunnable ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
  have hCur' : projectCurrent ctx observer s₁' = projectCurrent ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
  have hSvc' : projectServiceStatus ctx observer s₁' = projectServiceStatus ctx observer s₂' := by
    unfold storeObject at hStore₁ hStore₂
    cases hStore₁; cases hStore₂
    simpa [projectServiceStatus] using hSvcLow
  unfold lowEquivalent
  simp [projectState, hObj', hRun', hCur', hSvc']

-- ============================================================================
-- H-09 chain helpers for non-interference proofs
-- ============================================================================

/-- Filtering out an unobservable element from a list doesn't change a subsequent
filter by an observability predicate (the element would be filtered anyway). -/
private theorem filter_ne_then_filter_eq
    {α : Type} [DecidableEq α] (l : List α) (p : α → Bool) (a : α) (ha : p a = false) :
    (l.filter (· ≠ a)).filter p = l.filter p := by
  rw [List.filter_filter]
  congr 1
  funext x
  by_cases hx : x = a
  · subst hx; simp [ha]
  · simp [hx]

/-- H-09 (WS-E3): storeObject → storeTcbIpcState → removeRunnable chain preserves
projectState when all modified IDs are unobservable. -/
private theorem chain_store_tcb_removeRunnable_preserves_projectState
    (ctx : LabelingContext) (observer : IfObserver)
    (targetId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (obj : KernelObject) (ipc : ThreadIpcState)
    (st st1 st2 : SystemState)
    (hTargetHigh : objectObservable ctx observer targetId = false)
    (hTidHigh : threadObservable ctx observer tid = false)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hStore : storeObject targetId obj st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    projectState ctx observer (removeRunnable st2 tid) = projectState ctx observer st := by
  have hSchedEq : st2.scheduler = st.scheduler := by
    rw [storeTcbIpcState_preserves_scheduler st1 st2 tid ipc hTcb]
    exact storeObject_scheduler_eq st st1 targetId obj hStore
  have hSvcEq : st2.services = st.services := by
    rw [storeTcbIpcState_preserves_services st1 st2 tid ipc hTcb]
    exact storeObject_preserves_services st st1 targetId obj hStore
  unfold projectState; congr 1
  · funext oid
    by_cases hObs : objectObservable ctx observer oid
    · have hNeTarget : oid ≠ targetId := by intro h; subst h; simp [hTargetHigh] at hObs
      have hNeTid : oid ≠ tid.toObjId := by intro h; subst h; simp [hTidObjHigh] at hObs
      simp only [projectObjects, hObs, ite_true]
      rw [removeRunnable_preserves_objects,
          storeTcbIpcState_preserves_objects_ne st1 st2 tid ipc oid hNeTid hTcb,
          storeObject_objects_ne st st1 targetId oid obj hNeTarget hStore]
    · simp [projectObjects, hObs]
  · simp only [projectRunnable, removeRunnable_scheduler, hSchedEq]
    exact filter_ne_then_filter_eq st.scheduler.runnable (threadObservable ctx observer) tid hTidHigh
  · simp only [projectCurrent, removeRunnable_current, hSchedEq]
    cases hCur : st.scheduler.current with
    | none => simp
    | some curTid =>
      by_cases hEq : curTid = tid
      · subst hEq; simp [hTidHigh]
      · simp [show some curTid = some tid ↔ False from by constructor <;> simp [hEq]]
  · funext sid
    simp only [projectServiceStatus, lookupService, removeRunnable_preserves_services, hSvcEq]

/-- H-09 (WS-E3): storeObject → storeTcbIpcState → ensureRunnable chain preserves
projectState when all modified IDs are unobservable. -/
private theorem chain_store_tcb_ensureRunnable_preserves_projectState
    (ctx : LabelingContext) (observer : IfObserver)
    (targetId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (obj : KernelObject) (ipc : ThreadIpcState)
    (st st1 st2 : SystemState)
    (hTargetHigh : objectObservable ctx observer targetId = false)
    (hTidHigh : threadObservable ctx observer tid = false)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hStore : storeObject targetId obj st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    projectState ctx observer (ensureRunnable st2 tid) = projectState ctx observer st := by
  have hSchedEq : st2.scheduler = st.scheduler := by
    rw [storeTcbIpcState_preserves_scheduler st1 st2 tid ipc hTcb]
    exact storeObject_scheduler_eq st st1 targetId obj hStore
  have hSvcEq : st2.services = st.services := by
    rw [storeTcbIpcState_preserves_services st1 st2 tid ipc hTcb]
    exact storeObject_preserves_services st st1 targetId obj hStore
  unfold projectState; congr 1
  · funext oid
    by_cases hObs : objectObservable ctx observer oid
    · have hNeTarget : oid ≠ targetId := by intro h; subst h; simp [hTargetHigh] at hObs
      have hNeTid : oid ≠ tid.toObjId := by intro h; subst h; simp [hTidObjHigh] at hObs
      simp only [projectObjects, hObs, ite_true]
      rw [ensureRunnable_preserves_objects,
          storeTcbIpcState_preserves_objects_ne st1 st2 tid ipc oid hNeTid hTcb,
          storeObject_objects_ne st st1 targetId oid obj hNeTarget hStore]
    · simp [projectObjects, hObs]
  · simp only [projectRunnable, ensureRunnable_scheduler, hSchedEq]
    split
    · rfl
    · simp [List.filter_append, hTidHigh]
  · simp only [projectCurrent, ensureRunnable_preserves_current, hSchedEq]
  · funext sid
    simp only [projectServiceStatus, lookupService, ensureRunnable_preserves_services, hSvcEq]

/-- H-09 (WS-E3): Per-state helper showing endpointSend preserves the observer's
projection of a single state. Used by the two-state non-interference theorem. -/
private theorem endpointSend_preserves_projectState
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hSenderHigh : threadObservable ctx observer sender = false)
    (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hRecvHigh : ∀ (tid : SeLe4n.ThreadId) (ep : Endpoint),
      st.objects endpointId = some (.endpoint ep) →
      ep.waitingReceiver = some tid →
      threadObservable ctx observer tid = false ∧
      objectObservable ctx observer tid.toObjId = false)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointSend at hStep
  cases hEp : st.objects endpointId with
  | none => simp [hEp] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hEp] at hStep
    | endpoint ep =>
      simp only [hEp] at hStep
      cases hState : ep.state <;> simp only [hState] at hStep
      -- idle: storeObject → storeTcbIpcState → removeRunnable sender
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_store_tcb_removeRunnable_preserves_projectState
              ctx observer endpointId sender _ _ st st1 st2
              hEndpointHigh hSenderHigh hSenderObjHigh hStore hTcb
      -- send: storeObject → storeTcbIpcState → removeRunnable sender
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_store_tcb_removeRunnable_preserves_projectState
              ctx observer endpointId sender _ _ st st1 st2
              hEndpointHigh hSenderHigh hSenderObjHigh hStore hTcb
      -- receive: storeObject → storeTcbIpcState → ensureRunnable receiver
      · cases hQueue : ep.queue with
        | nil =>
          cases hWR : ep.waitingReceiver with
          | none => simp [hQueue, hWR] at hStep
          | some receiver =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                have ⟨hRecvThreadHigh, hRecvObjHigh⟩ := hRecvHigh receiver ep hEp hWR
                exact chain_store_tcb_ensureRunnable_preserves_projectState
                  ctx observer endpointId receiver _ _ st st1 st2
                  hEndpointHigh hRecvThreadHigh hRecvObjHigh hStore hTcb
        | cons _ _ => split at hStep <;> simp_all

-- ============================================================================
-- Non-interference theorem #1: endpointSend (existing, retained)
-- ============================================================================

/-- A successful endpoint send preserves low-equivalence for observers that cannot
see the sender thread and cannot observe the endpoint object itself.

Post H-09 (thread blocking): endpointSend now chains storeObject →
storeTcbIpcState → removeRunnable, so the proof must also show scheduler
changes preserve the projected runnable/current sets.

The additional hypotheses `hSenderObjHigh` and `hRecvHigh` are required because
H-09 makes endpointSend modify TCB objects (via storeTcbIpcState) and the
scheduler (via removeRunnable/ensureRunnable). In the receive branch, the
receiver thread comes from the endpoint's `waitingReceiver` field, which may
differ between the two states since the endpoint is unobservable. -/
theorem endpointSend_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSenderHigh : threadObservable ctx observer sender = false)
    (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hRecvHigh : ∀ (tid : SeLe4n.ThreadId) (ep : Endpoint),
      (s₁.objects endpointId = some (.endpoint ep) ∨
       s₂.objects endpointId = some (.endpoint ep)) →
      ep.waitingReceiver = some tid →
      threadObservable ctx observer tid = false ∧
      objectObservable ctx observer tid.toObjId = false)
    (hStep₁ : endpointSend endpointId sender s₁ = .ok ((), s₁'))
    (hStep₂ : endpointSend endpointId sender s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have h₁ := endpointSend_preserves_projectState ctx observer endpointId sender s₁ s₁'
    hSenderHigh hSenderObjHigh hEndpointHigh
    (fun tid ep h => hRecvHigh tid ep (Or.inl h)) hStep₁
  have h₂ := endpointSend_preserves_projectState ctx observer endpointId sender s₂ s₂'
    hSenderHigh hSenderObjHigh hEndpointHigh
    (fun tid ep h => hRecvHigh tid ep (Or.inr h)) hStep₂
  unfold lowEquivalent
  rw [h₁, h₂]
  exact hLow

-- ============================================================================
-- Non-interference theorem #2: chooseThread (WS-D2, F-05, TPI-D01)
-- ============================================================================

/-- Choosing the next thread does not leak high-domain scheduling decisions to
a low-clearance observer.

`chooseThread` is a read-only operation that does not mutate state. Since both
post-states equal their respective pre-states, low-equivalence is preserved
trivially. -/
theorem chooseThread_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (next₁ next₂ : Option SeLe4n.ThreadId)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : chooseThread s₁ = .ok (next₁, s₁'))
    (hStep₂ : chooseThread s₂ = .ok (next₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hEq₁ : s₁' = s₁ := chooseThread_preserves_state s₁ s₁' next₁ hStep₁
  have hEq₂ : s₂' = s₂ := chooseThread_preserves_state s₂ s₂' next₂ hStep₂
  subst hEq₁; subst hEq₂
  exact hLow

-- ============================================================================
-- Non-interference theorem #3: cspaceMint (WS-D2, F-05, TPI-D02)
-- ============================================================================

/-- Minting a capability in a non-observable CNode preserves low-equivalence.

If the destination CNode is not observable by the observer, the mint operation
only modifies non-projected state. The source lookup is read-only. -/
theorem cspaceMint_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (_hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep₁ : cspaceMint src dst rights badge s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceMint src dst rights badge s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  -- Decompose cspaceMint = lookup + mintDerivedCap + cspaceInsertSlot
  rcases cspaceMint_child_attenuates s₁ s₁' src dst rights badge hStep₁ with
    ⟨parent₁, child₁, hLookup₁, _, _⟩
  rcases cspaceMint_child_attenuates s₂ s₂' src dst rights badge hStep₂ with
    ⟨parent₂, child₂, hLookup₂, _, _⟩
  unfold cspaceMint at hStep₁ hStep₂
  rw [hLookup₁] at hStep₁; rw [hLookup₂] at hStep₂
  cases hMint₁ : mintDerivedCap parent₁ rights badge with
  | error e => simp [hMint₁] at hStep₁
  | ok c₁ =>
    cases hMint₂ : mintDerivedCap parent₂ rights badge with
    | error e => simp [hMint₂] at hStep₂
    | ok c₂ =>
      have hInsert₁ : cspaceInsertSlot dst c₁ s₁ = .ok ((), s₁') := by simpa [hMint₁] using hStep₁
      have hInsert₂ : cspaceInsertSlot dst c₂ s₂ = .ok ((), s₂') := by simpa [hMint₂] using hStep₂
      -- Use cspaceInsertSlot preservation helpers
      have hObjLow := congrArg ObservableState.objects hLow
      have hRunLow := congrArg ObservableState.runnable hLow
      have hCurLow := congrArg ObservableState.current hLow
      have hSched₁ := cspaceInsertSlot_preserves_scheduler s₁ s₁' dst c₁ hInsert₁
      have hSched₂ := cspaceInsertSlot_preserves_scheduler s₂ s₂' dst c₂ hInsert₂
      have hSvc₁ := cspaceInsertSlot_preserves_services s₁ s₁' dst c₁ hInsert₁
      have hSvc₂ := cspaceInsertSlot_preserves_services s₂ s₂' dst c₂ hInsert₂
      unfold lowEquivalent projectState
      congr 1
      · funext oid
        by_cases hObs : objectObservable ctx observer oid
        · have hNeDst : oid ≠ dst.cnode := by intro hEq; subst hEq; simp [hDstHigh] at hObs
          have hObj₁ := cspaceInsertSlot_preserves_objects_ne s₁ s₁' dst c₁ oid hNeDst hInsert₁
          have hObj₂ := cspaceInsertSlot_preserves_objects_ne s₂ s₂' dst c₂ oid hNeDst hInsert₂
          simp only [projectObjects, hObs, ite_true, hObj₁, hObj₂]
          have hBase := congrFun hObjLow oid
          simpa [projectState, projectObjects, hObs] using hBase
        · simp [projectObjects, hObs]
      · simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
      · simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
      · funext sid
        simp only [projectServiceStatus, lookupService]
        rw [show s₁'.services = s₁.services from hSvc₁, show s₂'.services = s₂.services from hSvc₂]
        have hBase := congrArg ObservableState.services hLow
        exact congrFun hBase sid

-- ============================================================================
-- Non-interference theorem #4: cspaceRevoke (WS-D2, F-05, TPI-D02)
-- ============================================================================

/-- Revoking capabilities in a non-observable CNode preserves low-equivalence.

If the CNode being revoked is not observable by the observer, the revoke operation
only modifies non-projected state. The operation goes through `storeObject` on the
CNode (filtered slots) then `clearCapabilityRefs` (lifecycle-only changes). Both
preserve scheduler and services. -/
theorem cspaceRevoke_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (addr : CSpaceAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCNodeHigh : objectObservable ctx observer addr.cnode = false)
    (hStep₁ : cspaceRevoke addr s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceRevoke addr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hObjLow := congrArg ObservableState.objects hLow
  have hRunLow := congrArg ObservableState.runnable hLow
  have hCurLow := congrArg ObservableState.current hLow
  have hSvcLow := congrArg ObservableState.services hLow
  -- Unfold cspaceRevoke to extract its staged decomposition
  unfold cspaceRevoke at hStep₁ hStep₂
  -- Process s₁ side
  cases hL₁ : cspaceLookupSlot addr s₁ with
  | error e => simp [hL₁] at hStep₁
  | ok p₁ =>
    rcases p₁ with ⟨par₁, stL₁⟩
    have hEq₁ : stL₁ = s₁ := cspaceLookupSlot_preserves_state s₁ stL₁ addr par₁ hL₁
    subst stL₁
    -- Process s₂ side
    cases hL₂ : cspaceLookupSlot addr s₂ with
    | error e => simp [hL₂] at hStep₂
    | ok p₂ =>
      rcases p₂ with ⟨par₂, stL₂⟩
      have hEq₂ : stL₂ = s₂ := cspaceLookupSlot_preserves_state s₂ stL₂ addr par₂ hL₂
      subst stL₂
      -- Case-split on the CNode object
      cases hC₁ : s₁.objects addr.cnode with
      | none => simp [hL₁, hC₁] at hStep₁
      | some o₁ =>
        cases o₁ with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hL₁, hC₁] at hStep₁
        | cnode cn₁ =>
          cases hC₂ : s₂.objects addr.cnode with
          | none => simp [hL₂, hC₂] at hStep₂
          | some o₂ =>
            cases o₂ with
            | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hL₂, hC₂] at hStep₂
            | cnode cn₂ =>
              -- Both sides reduce to storeObject + clearCapabilityRefs
              simp [hL₁, hC₁, storeObject] at hStep₁
              simp [hL₂, hC₂, storeObject] at hStep₂
              cases hStep₁; cases hStep₂
              -- Use clearCapabilityRefsState preservation lemmas
              unfold lowEquivalent projectState
              congr 1
              · -- objects: clearCapabilityRefsState preserves objects, storeObject only modifies addr.cnode
                funext oid
                by_cases hObs : objectObservable ctx observer oid
                · have hNe : oid ≠ addr.cnode := by
                    intro hEq; subst hEq; simp [hCNodeHigh] at hObs
                  have hBase : projectObjects ctx observer s₁ oid = projectObjects ctx observer s₂ oid :=
                    congrFun hObjLow oid
                  simp [projectObjects, hObs] at hBase ⊢
                  rw [clearCapabilityRefsState_preserves_objects, clearCapabilityRefsState_preserves_objects]
                  simp [hNe]
                  exact hBase
                · simp [projectObjects, hObs]
              · -- runnable: scheduler preserved by storeObject and clearCapabilityRefsState
                simp only [projectRunnable]
                rw [clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_scheduler]
                simpa [projectRunnable] using hRunLow
              · -- current: same
                simp only [projectCurrent]
                rw [clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_scheduler]
                simpa [projectCurrent] using hCurLow
              · -- services: preserved by storeObject and clearCapabilityRefsState
                funext sid
                simp only [projectServiceStatus, clearCapabilityRefsState_lookupService]
                have hBase := congrArg ObservableState.services hLow
                have hSidBase := congrFun hBase sid
                simpa [projectServiceStatus] using hSidBase

-- ============================================================================
-- Non-interference theorem #5: lifecycleRetypeObject (WS-D2, F-05, TPI-D03)
-- ============================================================================

/-- Retyping an object that is not observable by the observer preserves
low-equivalence.

If the target object being retyped is outside the observer's clearance, the
observer's view of the system state is unaffected. -/
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
  exact storeObject_at_unobservable_preserves_lowEquivalent
    ctx observer target newObj newObj s₁ s₂ s₁' s₂' hLow hTargetHigh hStore₁ hStore₂

end SeLe4n.Kernel
