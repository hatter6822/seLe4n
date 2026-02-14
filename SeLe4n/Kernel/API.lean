import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Minimal scheduling well-formedness condition for the bootstrap model. -/
def schedulerWellFormed (s : SchedulerState) : Prop :=
  match s.current with
  | none => True
  | some tid => tid ∈ s.runnable

/-- Scheduler invariant component #3 (M1 bundle v1): queue/current consistency.

Policy choice for this model is **strict**: when `current = some tid`, `tid` must appear in the
runnable queue. The relaxed policy (allowing absence while blocked/idle) is intentionally deferred
until explicit blocked/idle scheduler state is modeled. -/
def queueCurrentConsistent (s : SchedulerState) : Prop :=
  match s.current with
  | none => True
  | some tid => tid ∈ s.runnable

/-- Scheduler invariant component #1 (M1 bundle v1): runnable queue has no duplicate TIDs. -/
def runQueueUnique (s : SchedulerState) : Prop :=
  s.runnable.Nodup

/-- Scheduler invariant component #2 (M1 bundle v1): the selected current thread, if any,
resolves to a TCB in the object store. -/
def currentThreadValid (st : SystemState) : Prop :=
  match st.scheduler.current with
  | none => True
  | some tid => ∃ tcb : TCB, st.objects tid = some (.tcb tcb)

/-- Invariant bundle that should eventually mirror seL4 proof obligations. -/
def kernelInvariant (st : SystemState) : Prop :=
  queueCurrentConsistent st.scheduler ∧ runQueueUnique st.scheduler ∧ currentThreadValid st

/-- Scheduler Invariant Bundle v1 entrypoint used by milestone wording in the spec/docs.
This is an alias of `kernelInvariant` to keep theorem names aligned with the development guide
without changing existing proof call sites. -/
abbrev schedulerInvariantBundle (st : SystemState) : Prop :=
  kernelInvariant st

theorem schedulerWellFormed_iff_queueCurrentConsistent (s : SchedulerState) :
    schedulerWellFormed s ↔ queueCurrentConsistent s := by
  simp [schedulerWellFormed, queueCurrentConsistent]

theorem queueCurrentConsistent_when_no_current
    (s : SchedulerState)
    (hNone : s.current = none) :
    queueCurrentConsistent s := by
  simp [queueCurrentConsistent, hNone]

/-- Address of a capability slot in the modeled CSpace. -/
abbrev CSpaceAddr := SlotRef

/-- Rights attenuation policy for the M2 foundation slice.

`derived.rights` must be a subset of `parent.rights`; targets are preserved by mint-like
derivation in this slice. -/
def capAttenuates (parent derived : Capability) : Prop :=
  derived.target = parent.target ∧ ∀ right, right ∈ derived.rights → right ∈ parent.rights

/-- Lookup a capability at `(cnode, slot)` with typed CNode checking. -/
def cspaceLookupSlot (addr : CSpaceAddr) : Kernel Capability :=
  fun st =>
    match SystemState.lookupSlotCap st addr with
    | some cap => .ok (cap, st)
    | none =>
        match st.objects addr.cnode with
        | some (.cnode _) => .error .invalidCapability
        | _ => .error .objectNotFound

/-- Insert or replace a capability in `(cnode, slot)`. -/
def cspaceInsertSlot (addr : CSpaceAddr) (cap : Capability) : Kernel Unit :=
  fun st =>
    match st.objects addr.cnode with
    | some (.cnode cn) =>
        let cn' := cn.insert addr.slot cap
        storeObject addr.cnode (.cnode cn') st
    | _ => .error .objectNotFound

theorem cspaceLookupSlot_ok_iff_lookupSlotCap
    (st : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability) :
    cspaceLookupSlot addr st = .ok (cap, st) ↔
      SystemState.lookupSlotCap st addr = some cap := by
  constructor
  · intro hOk
    unfold cspaceLookupSlot at hOk
    cases hLookup : SystemState.lookupSlotCap st addr with
    | none =>
        cases hObj : st.objects addr.cnode with
        | none => simp [hLookup, hObj] at hOk
        | some obj =>
            cases obj <;> simp [hLookup, hObj] at hOk
    | some cap' =>
        simp [hLookup] at hOk
        simpa [hOk] using hLookup
  · intro hCap
    unfold cspaceLookupSlot
    simp [hCap]

/-- Successful lookup yields slot ownership by the containing CNode object id. -/
theorem cspaceLookupSlot_ok_implies_ownsSlot
    (st : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hLookup : cspaceLookupSlot addr st = .ok (cap, st)) :
    SystemState.ownsSlot st addr.cnode addr := by
  have hCap : SystemState.lookupSlotCap st addr = some cap :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st addr cap).1 hLookup
  exact (SystemState.ownsSlot_iff st addr.cnode addr).2 ⟨rfl, ⟨cap, hCap⟩⟩

/-- Requested rights must be contained in allowed rights. -/
def rightsSubset (requested allowed : List AccessRight) : Bool :=
  requested.all (fun right => right ∈ allowed)

theorem rightsSubset_sound
    (requested allowed : List AccessRight)
    (hSubset : rightsSubset requested allowed = true) :
    ∀ right, right ∈ requested → right ∈ allowed := by
  intro right hMem
  unfold rightsSubset at hSubset
  have hDec : decide (right ∈ allowed) = true := (List.all_eq_true.mp hSubset) right hMem
  simpa using hDec

/-- Build a mint-like derived capability with explicit rights attenuation. -/
def mintDerivedCap (parent : Capability) (rights : List AccessRight)
    (badge : Option SeLe4n.Badge := parent.badge) : Except KernelError Capability :=
  if rightsSubset rights parent.rights then
    .ok { target := parent.target, rights := rights, badge := badge }
  else
    .error .invalidCapability

/-- Mint from source slot and insert into destination slot under attenuation checks. -/
def cspaceMint
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge := none) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (parent, st') =>
        match mintDerivedCap parent rights badge with
        | .error e => .error e
        | .ok child => cspaceInsertSlot dst child st'

/-- Slot-level uniqueness/no-alias policy: lookup is deterministic for each slot address. -/
def cspaceSlotUnique (st : SystemState) : Prop :=
  ∀ addr cap₁ cap₂ st₁ st₂,
    cspaceLookupSlot addr st = .ok (cap₁, st₁) →
    cspaceLookupSlot addr st = .ok (cap₂, st₂) →
    cap₁ = cap₂

/-- Lookup soundness policy: successful lookup corresponds to concrete `(cnode, slot)` content. -/
def cspaceLookupSound (st : SystemState) : Prop :=
  ∀ addr cap st',
    cspaceLookupSlot addr st = .ok (cap, st') →
    ∃ cn, st.objects addr.cnode = some (.cnode cn) ∧ cn.lookup addr.slot = some cap

/-- Attenuation rule component used by the M2 capability invariant bundle. -/
def cspaceAttenuationRule : Prop :=
  ∀ parent child rights badge,
    mintDerivedCap parent rights badge = .ok child →
    capAttenuates parent child

/-- M2 foundation capability invariant bundle entrypoint. -/
def capabilityInvariantBundle (st : SystemState) : Prop :=
  cspaceSlotUnique st ∧ cspaceLookupSound st ∧ cspaceAttenuationRule

theorem cspaceLookupSlot_preserves_state
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceLookupSlot addr st = .ok (cap, st')) :
    st' = st := by
  unfold cspaceLookupSlot at hStep
  cases hLookup : SystemState.lookupSlotCap st addr with
  | none =>
      cases hObj : st.objects addr.cnode with
      | none => simp [hLookup, hObj] at hStep
      | some obj =>
          cases obj <;> simp [hLookup, hObj] at hStep
  | some foundCap =>
      simp [hLookup] at hStep
      exact hStep.2.symm

theorem cspaceInsertSlot_lookup_eq
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    cspaceLookupSlot addr st' = .ok (cap, st') := by
  rcases addr with ⟨cnodeId, slot⟩
  cases hObj : st.objects cnodeId with
  | none => simp [cspaceInsertSlot, hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [cspaceInsertSlot, hObj] at hStep
      | endpoint ep => simp [cspaceInsertSlot, hObj] at hStep
      | cnode cn =>
          simp [cspaceInsertSlot, hObj] at hStep
          cases hStep
          simp [cspaceLookupSlot, SystemState.lookupSlotCap, SystemState.lookupCNode, CNode.lookup, CNode.insert]

theorem cspaceInsertSlot_establishes_ownsSlot
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    SystemState.ownsSlot st' addr.cnode addr := by
  have hLookup : cspaceLookupSlot addr st' = .ok (cap, st') :=
    cspaceInsertSlot_lookup_eq st st' addr cap hStep
  exact cspaceLookupSlot_ok_implies_ownsSlot st' addr cap hLookup

theorem mintDerivedCap_attenuates
    (parent child : Capability)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    capAttenuates parent child := by
  by_cases hSubset : rightsSubset rights parent.rights = true
  · simp [mintDerivedCap, hSubset] at hMint
    cases hMint
    constructor
    · rfl
    · exact rightsSubset_sound rights parent.rights hSubset
  · simp [mintDerivedCap, hSubset] at hMint

theorem cspaceMint_child_attenuates
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    ∃ parent child,
      cspaceLookupSlot src st = .ok (parent, st) ∧
      cspaceLookupSlot dst st' = .ok (child, st') ∧
      capAttenuates parent child := by
  unfold cspaceMint at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src parent hSrc
      subst st1
      cases hMint : mintDerivedCap parent rights badge with
      | error e => simp [hSrc, hMint] at hStep
      | ok child =>
          have hAtt : capAttenuates parent child :=
            mintDerivedCap_attenuates parent child rights badge hMint
          have hInsert : cspaceInsertSlot dst child st = .ok ((), st') := by
            simpa [hSrc, hMint] using hStep
          refine ⟨parent, child, ?_, ?_, hAtt⟩
          · rfl
          · exact cspaceInsertSlot_lookup_eq st st' dst child hInsert

theorem cspaceSlotUnique_holds (st : SystemState) :
    cspaceSlotUnique st := by
  intro addr cap₁ cap₂ st₁ st₂ h₁ h₂
  have hSt₁ : st₁ = st := cspaceLookupSlot_preserves_state st st₁ addr cap₁ h₁
  have hSt₂ : st₂ = st := cspaceLookupSlot_preserves_state st st₂ addr cap₂ h₂
  subst st₁
  subst st₂
  have hEq : (.ok (cap₁, st) : Except KernelError (Capability × SystemState)) = .ok (cap₂, st) := by
    simpa [h₁] using h₂
  cases hEq
  rfl

theorem cspaceLookupSound_holds (st : SystemState) :
    cspaceLookupSound st := by
  intro addr cap st' hStep
  have hEq : st' = st := cspaceLookupSlot_preserves_state st st' addr cap hStep
  have hOk : cspaceLookupSlot addr st = .ok (cap, st) := by
    simpa [hEq] using hStep
  have hCap : SystemState.lookupSlotCap st addr = some cap :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st addr cap).1 hOk
  unfold SystemState.lookupSlotCap SystemState.lookupCNode at hCap
  cases hObj : st.objects addr.cnode with
  | none => simp [hObj] at hCap
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hCap
      | endpoint ep => simp [hObj] at hCap
      | cnode cn =>
          simp [hObj] at hCap
          exact ⟨cn, rfl, hCap⟩

theorem capabilityInvariantBundle_holds (st : SystemState) :
    capabilityInvariantBundle st := by
  refine ⟨cspaceSlotUnique_holds st, cspaceLookupSound_holds st, ?_⟩
  intro parent child rights badge hMint
  exact mintDerivedCap_attenuates parent child rights badge hMint

theorem cspaceLookupSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceLookupSlot addr st = .ok (cap, st')) :
    capabilityInvariantBundle st' := by
  have hEq : st' = st := cspaceLookupSlot_preserves_state st st' addr cap hStep
  subst hEq
  simpa using hInv

theorem cspaceInsertSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (_hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  exact capabilityInvariantBundle_holds st'

/-- Choose the first runnable thread, if any. -/
def chooseThread : Kernel (Option SeLe4n.ThreadId) :=
  fun st =>
    match st.scheduler.runnable with
    | [] => .ok (none, st)
    | t :: _ => .ok (some t, st)

/-- Simple scheduler step for the bootstrap model. If the selected runnable TID does not map
to a TCB object, the scheduler clears `current` instead of selecting an invalid thread. -/
def schedule : Kernel Unit :=
  fun st =>
    match st.scheduler.runnable with
    | [] => setCurrentThread none st
    | t :: _ =>
        match st.objects t with
        | some (.tcb _) => setCurrentThread (some t) st
        | _ => setCurrentThread none st

/-- Placeholder syscall dispatcher with one implemented path for now. -/
def handleYield : Kernel Unit :=
  schedule

theorem schedule_eq_chooseThread_then_setCurrent :
    schedule = (fun st =>
      match chooseThread st with
      | .error e => .error e
      | .ok (next, st') =>
          match next with
          | none => setCurrentThread none st'
          | some tid =>
              match st'.objects tid with
              | some (.tcb _) => setCurrentThread (some tid) st'
              | _ => setCurrentThread none st') := by
  funext st
  cases hRun : st.scheduler.runnable with
  | nil =>
      simp [schedule, chooseThread, setCurrentThread, hRun]
  | cons t ts =>
      cases hObj : st.objects t <;>
      simp [schedule, chooseThread, setCurrentThread, hRun, hObj]

theorem setCurrentThread_preserves_wellFormed
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hMem : tid ∈ st.scheduler.runnable)
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  simp [setCurrentThread] at hStep
  cases hStep
  simp [schedulerWellFormed, hMem]

theorem setCurrentThread_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hMem : tid ∈ st.scheduler.runnable)
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    queueCurrentConsistent st'.scheduler := by
  simp [setCurrentThread] at hStep
  cases hStep
  simp [queueCurrentConsistent, hMem]

theorem setCurrentThread_preserves_runQueueUnique
    (st st' : SystemState)
    (tid : Option SeLe4n.ThreadId)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : setCurrentThread tid st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  simp [setCurrentThread] at hStep
  cases hStep
  simpa [runQueueUnique] using hUnique

theorem setCurrentThread_none_preserves_currentThreadValid
    (st st' : SystemState)
    (hStep : setCurrentThread none st = .ok ((), st')) :
    currentThreadValid st' := by
  simp [setCurrentThread] at hStep
  cases hStep
  simp [currentThreadValid]

theorem setCurrentThread_some_preserves_currentThreadValid
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hObj : ∃ tcb : TCB, st.objects tid = some (.tcb tcb))
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    currentThreadValid st' := by
  simp [setCurrentThread] at hStep
  cases hStep
  simpa [currentThreadValid] using hObj

theorem chooseThread_returns_runnable_or_none
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hStep : chooseThread st = .ok (next, st')) :
    st' = st ∧
      ((next = none ∧ st.scheduler.runnable = []) ∨
       ∃ tid, next = some tid ∧ tid ∈ st.scheduler.runnable) := by
  cases hRun : st.scheduler.runnable with
  | nil =>
      simp [chooseThread, hRun] at hStep
      rcases hStep with ⟨hNext, hSt⟩
      have hNext' : next = none := hNext.symm
      subst hNext'
      subst hSt
      exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | cons t ts =>
      simp [chooseThread, hRun] at hStep
      rcases hStep with ⟨hNext, hSt⟩
      have hNext' : next = some t := hNext.symm
      subst hNext'
      subst hSt
      exact ⟨rfl, Or.inr ⟨t, rfl, by simp⟩⟩

theorem schedule_preserves_wellFormed
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  cases hRun : st.scheduler.runnable with
  | nil =>
      simp [schedule, setCurrentThread, hRun] at hStep
      cases hStep
      simp [schedulerWellFormed]
  | cons t ts =>
      cases hObj : st.objects t with
      | none =>
          simp [schedule, setCurrentThread, hRun, hObj] at hStep
          cases hStep
          simp [schedulerWellFormed]
      | some obj =>
          cases obj with
          | tcb tcb =>
              simp [schedule, setCurrentThread, hRun, hObj] at hStep
              cases hStep
              simp [schedulerWellFormed]
          | endpoint ep =>
              simp [schedule, setCurrentThread, hRun, hObj] at hStep
              cases hStep
              simp [schedulerWellFormed]
          | cnode cn =>
              simp [schedule, setCurrentThread, hRun, hObj] at hStep
              cases hStep
              simp [schedulerWellFormed]

theorem chooseThread_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hConsistent : queueCurrentConsistent st.scheduler)
    (hStep : chooseThread st = .ok (next, st')) :
    queueCurrentConsistent st'.scheduler := by
  rcases chooseThread_returns_runnable_or_none st st' next hStep with ⟨hSt, _⟩
  subst hSt
  simpa using hConsistent

theorem schedule_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    queueCurrentConsistent st'.scheduler := by
  cases hRun : st.scheduler.runnable with
  | nil =>
      simp [schedule, setCurrentThread, hRun] at hStep
      cases hStep
      simp [queueCurrentConsistent]
  | cons t ts =>
      cases hObj : st.objects t with
      | none =>
          simp [schedule, setCurrentThread, hRun, hObj] at hStep
          cases hStep
          simp [queueCurrentConsistent]
      | some obj =>
          cases obj with
          | tcb tcb =>
              exact setCurrentThread_preserves_queueCurrentConsistent st st' t
                (by simp [hRun])
                (by simpa [schedule, hRun, hObj] using hStep)
          | endpoint ep =>
              simp [schedule, setCurrentThread, hRun, hObj] at hStep
              cases hStep
              simp [queueCurrentConsistent]
          | cnode cn =>
              simp [schedule, setCurrentThread, hRun, hObj] at hStep
              cases hStep
              simp [queueCurrentConsistent]

theorem handleYield_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    queueCurrentConsistent st'.scheduler := by
  simpa [handleYield] using schedule_preserves_queueCurrentConsistent st st' hStep

theorem chooseThread_preserves_runQueueUnique
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : chooseThread st = .ok (next, st')) :
    runQueueUnique st'.scheduler := by
  rcases chooseThread_returns_runnable_or_none st st' next hStep with ⟨hSt, _⟩
  subst hSt
  simpa using hUnique

theorem chooseThread_preserves_currentThreadValid
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hValid : currentThreadValid st)
    (hStep : chooseThread st = .ok (next, st')) :
    currentThreadValid st' := by
  rcases chooseThread_returns_runnable_or_none st st' next hStep with ⟨hSt, _⟩
  subst hSt
  simpa using hValid

theorem schedule_preserves_runQueueUnique
    (st st' : SystemState)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : schedule st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  cases hRun : st.scheduler.runnable with
  | nil =>
      exact setCurrentThread_preserves_runQueueUnique st st' none hUnique (by
        simpa [schedule, hRun] using hStep)
  | cons t ts =>
      cases hObj : st.objects t with
      | none =>
          exact setCurrentThread_preserves_runQueueUnique st st' none hUnique (by
            simpa [schedule, hRun, hObj] using hStep)
      | some obj =>
          cases obj with
          | tcb tcb =>
              exact setCurrentThread_preserves_runQueueUnique st st' (some t) hUnique (by
                simpa [schedule, hRun, hObj] using hStep)
          | endpoint ep =>
              exact setCurrentThread_preserves_runQueueUnique st st' none hUnique (by
                simpa [schedule, hRun, hObj] using hStep)
          | cnode cn =>
              exact setCurrentThread_preserves_runQueueUnique st st' none hUnique (by
                simpa [schedule, hRun, hObj] using hStep)

theorem schedule_preserves_currentThreadValid
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    currentThreadValid st' := by
  cases hRun : st.scheduler.runnable with
  | nil =>
      exact setCurrentThread_none_preserves_currentThreadValid st st' (by
        simpa [schedule, hRun] using hStep)
  | cons t ts =>
      cases hObj : st.objects t with
      | none =>
          exact setCurrentThread_none_preserves_currentThreadValid st st' (by
            simpa [schedule, hRun, hObj] using hStep)
      | some obj =>
          cases obj with
          | tcb tcb =>
              exact setCurrentThread_some_preserves_currentThreadValid st st' t
                ⟨tcb, hObj⟩
                (by simpa [schedule, hRun, hObj] using hStep)
          | endpoint ep =>
              exact setCurrentThread_none_preserves_currentThreadValid st st' (by
                simpa [schedule, hRun, hObj] using hStep)
          | cnode cn =>
              exact setCurrentThread_none_preserves_currentThreadValid st st' (by
                simpa [schedule, hRun, hObj] using hStep)

theorem handleYield_preserves_wellFormed
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  simpa [handleYield] using schedule_preserves_wellFormed st st' hStep

theorem handleYield_preserves_runQueueUnique
    (st st' : SystemState)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : handleYield st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  simpa [handleYield] using schedule_preserves_runQueueUnique st st' hUnique hStep

theorem handleYield_preserves_currentThreadValid
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    currentThreadValid st' := by
  simpa [handleYield] using schedule_preserves_currentThreadValid st st' hStep

theorem chooseThread_preserves_kernelInvariant
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hInv : kernelInvariant st)
    (hStep : chooseThread st = .ok (next, st')) :
    kernelInvariant st' := by
  exact ⟨
    chooseThread_preserves_queueCurrentConsistent st st' next hInv.1 hStep,
    chooseThread_preserves_runQueueUnique st st' next hInv.2.1 hStep,
    chooseThread_preserves_currentThreadValid st st' next hInv.2.2 hStep
  ⟩

theorem schedule_preserves_kernelInvariant
    (st st' : SystemState)
    (hInv : kernelInvariant st)
    (hStep : schedule st = .ok ((), st')) :
    kernelInvariant st' := by
  exact ⟨schedule_preserves_queueCurrentConsistent st st' hStep,
    schedule_preserves_runQueueUnique st st' hInv.2.1 hStep,
    schedule_preserves_currentThreadValid st st' hStep⟩

theorem handleYield_preserves_kernelInvariant
    (st st' : SystemState)
    (hInv : kernelInvariant st)
    (hStep : handleYield st = .ok ((), st')) :
    kernelInvariant st' := by
  simpa [handleYield] using schedule_preserves_kernelInvariant st st' hInv hStep

theorem chooseThread_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : chooseThread st = .ok (next, st')) :
    schedulerInvariantBundle st' := by
  exact chooseThread_preserves_kernelInvariant st st' next hInv hStep

theorem schedule_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : schedule st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  exact schedule_preserves_kernelInvariant st st' hInv hStep

theorem handleYield_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  exact handleYield_preserves_kernelInvariant st st' hInv hStep

end SeLe4n.Kernel
