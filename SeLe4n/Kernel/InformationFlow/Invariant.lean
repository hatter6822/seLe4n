import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.InformationFlow.Enforcement
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
-- WS-E5: clearCapabilityRefsState preserves projection (used by composed proofs)
-- ============================================================================

/-- clearCapabilityRefsState preserves the observer projection for any refs list. -/
private theorem clearCapabilityRefsState_preserves_projectState
    (ctx : LabelingContext) (observer : IfObserver)
    (refs : List SlotRef) (st : SystemState) :
    projectState ctx observer (clearCapabilityRefsState refs st) =
      projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext oid; simp [projectObjects, clearCapabilityRefsState_preserves_objects]
  · simp [projectRunnable, clearCapabilityRefsState_preserves_scheduler]
  · simp [projectCurrent, clearCapabilityRefsState_preserves_scheduler]
  · funext sid; simp [projectServiceStatus, clearCapabilityRefsState_lookupService]

-- ============================================================================
-- WS-E3/H-09: Multi-step operation helpers for non-interference
-- ============================================================================

/-- List filter commutation: filtering by (· ≠ a) then by p equals just filtering by p
when p a = false. Used for removeRunnable projection preservation. -/
private theorem list_filter_ne_then_filter_eq
    {α : Type} [DecidableEq α] (xs : List α) (a : α) (p : α → Bool)
    (hPa : p a = false) :
    (xs.filter (· ≠ a)).filter p = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter]
    by_cases hxeq : x = a
    · -- x = a: the (· ≠ a) filter drops x; p a = false drops it from RHS too
      subst hxeq
      simp only [ne_eq, not_true, decide_false, hPa]
      exact ih
    · -- x ≠ a: the (· ≠ a) filter keeps x
      have hNeTrue : decide (x ≠ a) = true := decide_eq_true_eq.mpr hxeq
      rw [hNeTrue]; simp only [List.filter]
      cases hpx : p x
      · exact ih
      · simp only [List.cons.injEq, true_and]; exact ih

/-- List filter absorption: filtering by p on (xs ++ [a]) equals filtering by p on xs
when p a = false. Used for ensureRunnable projection preservation. -/
private theorem list_filter_append_singleton_unobs
    {α : Type} [DecidableEq α] (xs : List α) (a : α) (p : α → Bool)
    (hPa : p a = false) :
    (xs ++ [a]).filter p = xs.filter p := by
  rw [List.filter_append]
  simp [List.filter, hPa]

/-- Removing a non-observable thread preserves low-equivalence projection. -/
private theorem removeRunnable_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hTidHigh : threadObservable ctx observer tid = false) :
    projectState ctx observer (removeRunnable st tid) = projectState ctx observer st := by
  have hRun : projectRunnable ctx observer (removeRunnable st tid) = projectRunnable ctx observer st := by
    simp only [projectRunnable, removeRunnable]
    exact list_filter_ne_then_filter_eq st.scheduler.runnable tid (threadObservable ctx observer) hTidHigh
  have hCur : projectCurrent ctx observer (removeRunnable st tid) = projectCurrent ctx observer st := by
    simp only [projectCurrent, removeRunnable]
    cases hC : st.scheduler.current with
    | none => simp
    | some x =>
      by_cases hEq : some x = some tid
      · rw [if_pos hEq]; cases (Option.some.inj hEq); simp [hTidHigh]
      · rw [if_neg hEq]
  have hObj : projectObjects ctx observer (removeRunnable st tid) = projectObjects ctx observer st := rfl
  have hSvc : projectServiceStatus ctx observer (removeRunnable st tid) =
      projectServiceStatus ctx observer st := funext fun _ => rfl
  simp only [projectState, hObj, hRun, hCur, hSvc]

/-- Adding a non-observable thread to runnable preserves low-equivalence projection. -/
private theorem ensureRunnable_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hTidHigh : threadObservable ctx observer tid = false) :
    projectState ctx observer (ensureRunnable st tid) = projectState ctx observer st := by
  unfold ensureRunnable
  split
  · rfl
  · split
    · have hRun : projectRunnable ctx observer
          { st with scheduler := { st.scheduler with runnable := st.scheduler.runnable ++ [tid] } } =
          projectRunnable ctx observer st := by
        simp only [projectRunnable]
        exact list_filter_append_singleton_unobs st.scheduler.runnable tid (threadObservable ctx observer) hTidHigh
      have hObj : projectObjects ctx observer
          { st with scheduler := { st.scheduler with runnable := st.scheduler.runnable ++ [tid] } } =
          projectObjects ctx observer st := rfl
      have hCur : projectCurrent ctx observer
          { st with scheduler := { st.scheduler with runnable := st.scheduler.runnable ++ [tid] } } =
          projectCurrent ctx observer st := rfl
      have hSvc : projectServiceStatus ctx observer
          { st with scheduler := { st.scheduler with runnable := st.scheduler.runnable ++ [tid] } } =
          projectServiceStatus ctx observer st := funext fun _ => rfl
      simp only [projectState, hObj, hRun, hCur, hSvc]
    · rfl

/-- storeTcbIpcState at a non-observable object preserves projection (single-state). -/
private theorem storeTcbIpcState_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none =>
    simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => cases hStore
    | ok pair =>
      simp only [hStore] at hStep
      have := Except.ok.inj hStep; subst this
      simp only [projectState]; congr 1
      · -- projectObjects: storeObject at non-observable tid.toObjId
        funext oid
        by_cases hObs : objectObservable ctx observer oid
        · simp [projectObjects, hObs]
          by_cases hEq : oid = tid.toObjId
          · subst hEq; simp [hTidObjHigh] at hObs
          · exact storeObject_objects_ne st pair.2 tid.toObjId oid _ hEq hStore
        · simp [projectObjects, hObs]
      · -- projectRunnable: scheduler preserved by storeObject
        simp [projectRunnable, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- projectCurrent: scheduler preserved by storeObject
        simp [projectCurrent, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- projectServiceStatus: services unchanged
        unfold storeObject at hStore; cases hStore; funext sid; rfl

/-- storeObject at a non-observable object preserves projection (single-state). -/
private theorem storeObject_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hOidHigh : objectObservable ctx observer oid = false)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext o
    by_cases hObs : objectObservable ctx observer o
    · simp [projectObjects, hObs]
      by_cases hEq : o = oid
      · subst hEq; simp [hOidHigh] at hObs
      · exact storeObject_objects_ne st st' oid o obj hEq hStore
    · simp [projectObjects, hObs]
  · simp [projectRunnable, storeObject_scheduler_eq st st' oid obj hStore]
  · simp [projectCurrent, storeObject_scheduler_eq st st' oid obj hStore]
  · unfold storeObject at hStore; cases hStore; funext sid; rfl

/-- WS-E3/H-09: endpointSend at non-observable entities preserves projection (single execution). -/
private theorem endpointSend_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hSenderHigh : threadObservable ctx observer sender = false)
    (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hRecvDomain : ∀ ep tid, st.objects endpointId = some (.endpoint ep) →
        ep.waitingReceiver = some tid → threadObservable ctx observer tid = false)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : ep.state with
  | idle =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        rw [removeRunnable_preserves_projection ctx observer st2 sender hSenderHigh,
            storeTcbIpcState_preserves_projection ctx observer pair.2 st2 sender _ hSenderObjHigh hTcb,
            storeObject_preserves_projection ctx observer st pair.2 endpointId _ hEndpointHigh hStore]
  | send =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        rw [removeRunnable_preserves_projection ctx observer st2 sender hSenderHigh,
            storeTcbIpcState_preserves_projection ctx observer pair.2 st2 sender _ hSenderObjHigh hTcb,
            storeObject_preserves_projection ctx observer st pair.2 endpointId _ hEndpointHigh hStore]
  | receive =>
    simp [endpointSend, hObj, hState] at hStep
    cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;> simp [hQueue, hWait] at hStep
    case nil.some receiver =>
      have hRecvHigh := hRecvDomain ep receiver hObj hWait
      have hRecvObjHigh := hCoherent receiver hRecvHigh
      revert hStep
      cases hStore : storeObject endpointId _ st with
      | error e => simp
      | ok pair =>
        simp only []
        cases hTcb : storeTcbIpcState pair.2 receiver _ with
        | error e => simp
        | ok st2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
          rw [ensureRunnable_preserves_projection ctx observer st2 receiver hRecvHigh,
              storeTcbIpcState_preserves_projection ctx observer pair.2 st2 receiver _ hRecvObjHigh hTcb,
              storeObject_preserves_projection ctx observer st pair.2 endpointId _ hEndpointHigh hStore]

-- ============================================================================
-- Non-interference theorem #1: endpointSend (existing, retained)
-- ============================================================================

/-- A successful endpoint send preserves low-equivalence for observers that cannot
see the sender thread and cannot observe the endpoint object itself.

WS-E3/H-09: Updated for multi-step chain (storeObject → storeTcbIpcState →
removeRunnable/ensureRunnable). Additional hypotheses required:
- `hSenderObjHigh`: sender's TCB object is non-observable
- `hCoherent`: thread-level non-observability implies object-level non-observability
- `hRecvDomain₁`/`hRecvDomain₂`: threads blocking on the endpoint are non-observable
  (ensures the receive-path handshake doesn't leak to the observer). -/
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
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hRecvDomain₁ : ∀ ep tid, s₁.objects endpointId = some (.endpoint ep) →
        ep.waitingReceiver = some tid → threadObservable ctx observer tid = false)
    (hRecvDomain₂ : ∀ ep tid, s₂.objects endpointId = some (.endpoint ep) →
        ep.waitingReceiver = some tid → threadObservable ctx observer tid = false)
    (hStep₁ : endpointSend endpointId sender s₁ = .ok ((), s₁'))
    (hStep₂ : endpointSend endpointId sender s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  -- Strategy: show projectState is preserved by each step on both states independently,
  -- then chain with the low-equivalence hypothesis.
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    -- Prove s₂ projection preserved (symmetric to s₁)
    exact endpointSend_projection_preserved ctx observer endpointId sender s₂ s₂'
      hEndpointHigh hSenderHigh hSenderObjHigh hCoherent hRecvDomain₂ hStep₂
  -- Prove s₁ projection preserved
  exact endpointSend_projection_preserved ctx observer endpointId sender s₁ s₁'
    hEndpointHigh hSenderHigh hSenderObjHigh hCoherent hRecvDomain₁ hStep₁

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

-- ============================================================================
-- WS-E5/H-05: Bundle-level composed non-interference (IF-M4)
-- ============================================================================

/-! ## H-05 — Composed Bundle Non-Interference

This section lifts the IF-M3 transition-level non-interference seeds into
IF-M4 bundle-level composition. The architecture is:

1. `NonInterferenceStep` — inductive encoding the 5 operation families with
   their domain-separation hypotheses.
2. `step_preserves_projection` — one-sided projection preservation for
   any single step.
3. `composedNonInterference_step` — the primary IF-M4 theorem: a single
   non-interference step on two low-equivalent states yields low-equivalent
   post-states.
4. `NonInterferenceTrace` — multi-step trace inductive.
5. `composedNonInterference_trace` — trace-level IF-M4 composition.
6. `endpointSend_then_cspaceMint_preserves_lowEquivalent` — concrete
   cross-subsystem composed witness (from PR #219 synthesis). -/

/-- WS-E5/H-05: Inductive covering the 5 IF-M3 operation families with their
full parameter sets and domain-separation hypotheses.

Each constructor witnesses that a specific kernel operation, applied to a state,
produces a post-state while satisfying all the domain-separation hypotheses
required for non-interference. -/
inductive NonInterferenceStep
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) : Prop where
  | chooseThread
      (next : Option SeLe4n.ThreadId)
      (hStep : chooseThread st = .ok (next, st'))
    : NonInterferenceStep ctx observer st st'
  | endpointSend
      (eid : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
      (hEndpointHigh : objectObservable ctx observer eid = false)
      (hSenderHigh : threadObservable ctx observer sender = false)
      (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
      (hCoherent : ∀ tid : SeLe4n.ThreadId,
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hRecvDomain : ∀ ep tid, st.objects eid = some (.endpoint ep) →
          ep.waitingReceiver = some tid → threadObservable ctx observer tid = false)
      (hStep : endpointSend eid sender st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceMint
      (src dst : CSpaceAddr) (rights : List AccessRight) (badge : Option SeLe4n.Badge)
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

/-- WS-E5/H-05: A single non-interference step preserves the observer's
projection (one-sided version). -/
theorem step_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hStep : NonInterferenceStep ctx observer st st') :
    projectState ctx observer st' = projectState ctx observer st := by
  cases hStep with
  | chooseThread next hOp =>
    have := chooseThread_preserves_state st st' next hOp; subst this; rfl
  | endpointSend eid sender hEH hSH hSOH hCo hRD hOp =>
    exact endpointSend_projection_preserved ctx observer eid sender st st'
      hEH hSH hSOH hCo hRD hOp
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
          · exact cspaceInsertSlot_preserves_objects_ne st st' dst c oid hEq hInsert
        · simp [projectObjects, hObs]
      · simp [projectRunnable, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · simp [projectCurrent, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · funext sid
        simp only [projectServiceStatus, lookupService,
          cspaceInsertSlot_preserves_services st st' dst c hInsert]
  | cspaceRevoke addr hAddrH hOp =>
    -- Reuse the one-sided projection preservation pattern from the existing
    -- two-sided cspaceRevoke_preserves_lowEquivalent proof.
    unfold cspaceRevoke at hOp
    cases hL : cspaceLookupSlot addr st with
    | error e => simp [hL] at hOp
    | ok p =>
      rcases p with ⟨par, stL⟩
      have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL addr par hL
      subst stL
      cases hC : st.objects addr.cnode with
      | none => simp [hL, hC] at hOp
      | some obj =>
        cases obj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hL, hC] at hOp
        | cnode cn =>
          simp [hL, hC, storeObject] at hOp; cases hOp
          rw [clearCapabilityRefsState_preserves_projectState]
          simp only [projectState]; congr 1
          funext oid; by_cases hObs : objectObservable ctx observer oid
          · simp [projectObjects, hObs]
            have hNe : oid ≠ addr.cnode := by
              intro hEq; subst hEq; simp [hAddrH] at hObs
            simp [hNe]
          · simp [projectObjects, hObs]
  | lifecycleRetype authority target newObj hTH hOp =>
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hOp with
      ⟨_, _, _, _, _, _, hStore⟩
    exact storeObject_preserves_projection ctx observer st st' target newObj hTH hStore

/-- WS-E5/H-05: Primary IF-M4 composition theorem — single-step bundle
non-interference.

If two states are low-equivalent, and a non-interference step is applied to
each, the resulting states remain low-equivalent. -/
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

/-- WS-E5/H-05: Multi-step trace of non-interference steps. -/
inductive NonInterferenceTrace
    (ctx : LabelingContext) (observer : IfObserver) :
    SystemState → SystemState → Prop where
  | nil (st : SystemState) : NonInterferenceTrace ctx observer st st
  | cons (st₁ st₂ st₃ : SystemState)
      (hStep : NonInterferenceStep ctx observer st₁ st₂)
      (hTail : NonInterferenceTrace ctx observer st₂ st₃)
    : NonInterferenceTrace ctx observer st₁ st₃

/-- WS-E5/H-05: A non-interference trace preserves the observer's projection. -/
theorem trace_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hTrace : NonInterferenceTrace ctx observer st st') :
    projectState ctx observer st' = projectState ctx observer st := by
  induction hTrace with
  | nil _ => rfl
  | cons _ st₂ _ hStep _ ih =>
    rw [ih, step_preserves_projection ctx observer _ st₂ hStep]

/-- WS-E5/H-05: Trace-level IF-M4 composition theorem.

If two states start low-equivalent, and independent non-interference traces
execute on each, the final states remain low-equivalent. -/
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
-- WS-E5/H-05: Concrete cross-subsystem composed witness
-- ============================================================================

/-- WS-E5/H-05: Abstract non-interference predicate for a single kernel action.

`preservesLowEquivalence ctx observer action` holds when `action` applied to
any pair of low-equivalent states yields low-equivalent post-states, provided
neither succeeds while the other fails. -/
def preservesLowEquivalence
    (ctx : LabelingContext) (observer : IfObserver)
    (action : Kernel Unit) : Prop :=
  ∀ s₁ s₂ s₁' s₂' : SystemState,
    lowEquivalent ctx observer s₁ s₂ →
    action s₁ = .ok ((), s₁') →
    action s₂ = .ok ((), s₂') →
    lowEquivalent ctx observer s₁' s₂'

/-- WS-E5/H-05: Two-operation sequential composition preserves non-interference. -/
theorem compose_preservesLowEquivalence
    (ctx : LabelingContext) (observer : IfObserver)
    (op₁ op₂ : Kernel Unit)
    (h₁ : preservesLowEquivalence ctx observer op₁)
    (h₂ : preservesLowEquivalence ctx observer op₂) :
    preservesLowEquivalence ctx observer (fun st => match op₁ st with
      | .ok ((), st') => op₂ st'
      | .error e => .error e) := by
  intro s₁ s₂ s₁' s₂' hLow hComp₁ hComp₂
  -- Extract intermediate states from the sequential composition
  -- op₁ must succeed on s₁ for the composition to produce .ok
  match h1step : op₁ s₁, h2step : op₁ s₂ with
  | .error _, _ => simp [h1step] at hComp₁
  | _, .error _ => simp [h2step] at hComp₂
  | .ok ((), mid₁), .ok ((), mid₂) =>
    simp [h1step] at hComp₁
    simp [h2step] at hComp₂
    have hMid := h₁ s₁ s₂ mid₁ mid₂ hLow h1step h2step
    exact h₂ mid₁ mid₂ s₁' s₂' hMid hComp₁ hComp₂

/-- WS-E5/H-05: An action that produces an error preserves low-equivalence
(the post-state doesn't exist, so the property holds vacuously). -/
theorem errorAction_preserves_lowEquiv
    (ctx : LabelingContext) (observer : IfObserver)
    (err : KernelError) :
    preservesLowEquivalence ctx observer (fun _ => .error err) := by
  intro _ _ _ _ _ h₁ _; simp at h₁

end SeLe4n.Kernel
