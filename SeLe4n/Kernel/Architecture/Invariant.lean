/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.Adapter
import SeLe4n.Kernel.Architecture.VSpaceInvariant
import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.TlbModel
import SeLe4n.Kernel.Service.Invariant
import SeLe4n.Kernel.CrossSubsystem

/-!
# Architecture Boundary Invariant Proofs (M6)

This module defines the composed `proofLayerInvariantBundle` entrypoint that composes
all active subsystem invariant bundles, and the `AdapterProofHooks` structure that
ties architecture-adapter transitions to invariant preservation.

## Proof scope qualification (F-16)

Theorems in this module compose the subsystem-level invariants into global
architecture-boundary bundles. Preservation is inherited from the subsystem modules
(IPC, Capability, Lifecycle, Service, Scheduler, VSpace). See individual subsystem
invariant modules for per-theorem classification.

| Category | Theorems |
|---|---|
| **Substantive preservation** | `adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle`, `adapterWriteRegister_ok_preserves_proofLayerInvariantBundle`, `adapterReadMemory_ok_preserves_proofLayerInvariantBundle`, `adapterContextSwitch_ok_preserves_proofLayerInvariantBundle` |
| **Error-case preservation** | `adapterAdvanceTimer_error_invalidContext_preserves_proofLayerInvariantBundle`, `adapterAdvanceTimer_error_unsupportedBinding_preserves_proofLayerInvariantBundle`, `adapterWriteRegister_error_unsupportedBinding_preserves_proofLayerInvariantBundle`, `adapterReadMemory_error_unsupportedBinding_preserves_proofLayerInvariantBundle`, `adapterContextSwitch_error_unsupportedBinding_preserves_proofLayerInvariantBundle` |

The error-case preservation theorems are trivially true (the state is unchanged on
error). The success-path theorems are substantive: they prove that adapter transitions
satisfying the `RuntimeBoundaryContract` and `AdapterProofHooks` obligations preserve
the composed invariant bundle over genuinely changed state.

**AI6-C (M-18) — Cross-module composition gap**: Per-subsystem invariant
preservation is proven independently: TLB consistency (`tlbConsistent`),
cache coherency (`CacheModel.lean`), page table well-formedness
(`VSpaceInvariant.lean`), and ASID uniqueness (`AsidManager.lean`). The
relational composition theorem — proving that TLB + cache + page table
maintain *simultaneous* coherency through compound operations (e.g., a page
table update followed by TLB flush followed by I-cache invalidation) — is
not yet proven. Per-subsystem preservation suffices for the sequential model
where operations are atomic. The relational composition theorem is deferred
to WS-V hardware binding where non-atomic multi-step cache/TLB maintenance
sequences require cross-subsystem coherency proofs.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model
open SeLe4n.Kernel

/-- WS-M6-C composed theorem surface: architecture-adapter hooks over all active invariant bundles.

H-07 (WS-E3): `vspaceInvariantBundle` added to the composition, closing the gap
where VSpace ASID-uniqueness and non-overlap invariants were proven in isolation
but not included in the top-level composed bundle.

WS-H12e: Cross-subsystem invariant reconciliation — uses `schedulerInvariantBundleFull`
(which now includes `contextMatchesCurrent`) instead of the bare `schedulerInvariantBundle`,
and `coreIpcInvariantBundle` now subsumes `ipcInvariantFull` (including
`dualQueueSystemInvariant` and `allPendingMessagesBounded`). The
`ipcSchedulerCouplingInvariantBundle` now includes `contextMatchesCurrent` and
`currentThreadDequeueCoherent`. -/
def proofLayerInvariantBundle (st : SystemState) : Prop :=
  schedulerInvariantBundleFull st ∧
    capabilityInvariantBundle st ∧
    coreIpcInvariantBundle st ∧
    ipcSchedulerCouplingInvariantBundle st ∧
    lifecycleInvariantBundle st ∧
    serviceLifecycleCapabilityInvariantBundle st ∧
    vspaceInvariantBundle st ∧
    crossSubsystemInvariant st ∧
    tlbConsistent st st.tlb ∧
    schedulerInvariantBundleExtended st ∧
    notificationWaiterConsistent st

/-- Proof-carrying local preservation hooks required to compose adapter paths with invariant bundles. -/
structure AdapterProofHooks (contract : RuntimeBoundaryContract) where
  preserveAdvanceTimer :
    ∀ ticks st,
      proofLayerInvariantBundle st →
      contract.timerMonotonic st (advanceTimerState ticks st) →
      ticks ≠ 0 →
      proofLayerInvariantBundle (advanceTimerState ticks st)
  preserveWriteRegister :
    ∀ reg value st,
      proofLayerInvariantBundle st →
      contract.registerContextStable st (writeRegisterState reg value st) →
      proofLayerInvariantBundle (writeRegisterState reg value st)
  preserveReadMemory :
    ∀ addr st,
      proofLayerInvariantBundle st →
      contract.memoryAccessAllowed st addr →
      proofLayerInvariantBundle st
  preserveContextSwitch :
    ∀ newTid newRegs st,
      proofLayerInvariantBundle st →
      contract.registerContextStable st (contextSwitchState newTid newRegs st) →
      proofLayerInvariantBundle (contextSwitchState newTid newRegs st)

theorem adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle
    (contract : RuntimeBoundaryContract)
    (hooks : AdapterProofHooks contract)
    (ticks : Nat)
    (st st' : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (hStep : adapterAdvanceTimer contract ticks st = .ok ((), st')) :
    proofLayerInvariantBundle st' := by
  by_cases hTicks : ticks = 0
  · have hErr := adapterAdvanceTimer_error_invalidContext contract st
    subst ticks
    rw [hErr] at hStep
    simp at hStep
  · by_cases hMono : contract.timerMonotonic st (advanceTimerState ticks st)
    · simp [adapterAdvanceTimer, hTicks, hMono] at hStep
      cases hStep
      exact hooks.preserveAdvanceTimer ticks st hInv hMono hTicks
    · have hErr :=
        adapterAdvanceTimer_error_unsupportedBinding contract ticks st hTicks hMono
      rw [hErr] at hStep
      simp at hStep

theorem adapterWriteRegister_ok_preserves_proofLayerInvariantBundle
    (contract : RuntimeBoundaryContract)
    (hooks : AdapterProofHooks contract)
    (reg : SeLe4n.RegName)
    (value : SeLe4n.RegValue)
    (st st' : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (hStep : adapterWriteRegister contract reg value st = .ok ((), st')) :
    proofLayerInvariantBundle st' := by
  by_cases hStable : contract.registerContextStable st (writeRegisterState reg value st)
  · simp [adapterWriteRegister, hStable] at hStep
    cases hStep
    exact hooks.preserveWriteRegister reg value st hInv hStable
  · have hErr :=
      adapterWriteRegister_error_unsupportedBinding contract reg value st hStable
    rw [hErr] at hStep
    simp at hStep

theorem adapterReadMemory_ok_preserves_proofLayerInvariantBundle
    (contract : RuntimeBoundaryContract)
    (hooks : AdapterProofHooks contract)
    (addr : SeLe4n.PAddr)
    (st st' : SystemState)
    (byte : UInt8)
    (hInv : proofLayerInvariantBundle st)
    (hStep : adapterReadMemory contract addr st = .ok (byte, st')) :
    proofLayerInvariantBundle st' := by
  rcases adapterReadMemory_ok_returns_machine_byte contract addr st st' byte hStep with ⟨hStEq, _⟩
  subst st'
  have hAllow : contract.memoryAccessAllowed st addr := by
    by_cases hAllowed : contract.memoryAccessAllowed st addr
    · exact hAllowed
    · have hErr := adapterReadMemory_error_unsupportedBinding contract addr st hAllowed
      rw [hErr] at hStep
      simp at hStep
  exact hooks.preserveReadMemory addr st hInv hAllow

theorem adapterContextSwitch_ok_preserves_proofLayerInvariantBundle
    (contract : RuntimeBoundaryContract)
    (hooks : AdapterProofHooks contract)
    (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile)
    (st st' : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (hStep : adapterContextSwitch contract newTid newRegs st = .ok ((), st')) :
    proofLayerInvariantBundle st' := by
  by_cases hStable : contract.registerContextStable st (contextSwitchState newTid newRegs st)
  · simp [adapterContextSwitch, hStable] at hStep
    cases hStep
    exact hooks.preserveContextSwitch newTid newRegs st hInv hStable
  · have hErr :=
      adapterContextSwitch_error_unsupportedBinding contract newTid newRegs st hStable
    rw [hErr] at hStep
    simp at hStep

theorem adapterContextSwitch_error_unsupportedBinding_preserves_proofLayerInvariantBundle
    (contract : RuntimeBoundaryContract)
    (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile)
    (st : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (_hReject : ¬ contract.registerContextStable st (contextSwitchState newTid newRegs st))
    (_hErr : adapterContextSwitch contract newTid newRegs st =
      .error (mapAdapterError .unsupportedBinding)) :
    proofLayerInvariantBundle st :=
  hInv

theorem adapterAdvanceTimer_error_invalidContext_preserves_proofLayerInvariantBundle
    (contract : RuntimeBoundaryContract)
    (st : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (_hErr : adapterAdvanceTimer contract 0 st = .error (mapAdapterError .invalidContext)) :
    proofLayerInvariantBundle st :=
  hInv

theorem adapterAdvanceTimer_error_unsupportedBinding_preserves_proofLayerInvariantBundle
    (contract : RuntimeBoundaryContract)
    (ticks : Nat)
    (st : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (_hTicks : ticks ≠ 0)
    (_hReject : ¬ contract.timerMonotonic st (advanceTimerState ticks st))
    (_hErr : adapterAdvanceTimer contract ticks st = .error (mapAdapterError .unsupportedBinding)) :
    proofLayerInvariantBundle st :=
  hInv

theorem adapterWriteRegister_error_unsupportedBinding_preserves_proofLayerInvariantBundle
    (contract : RuntimeBoundaryContract)
    (reg : SeLe4n.RegName)
    (value : SeLe4n.RegValue)
    (st : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (_hReject : ¬ contract.registerContextStable st (writeRegisterState reg value st))
    (_hErr : adapterWriteRegister contract reg value st = .error (mapAdapterError .unsupportedBinding)) :
    proofLayerInvariantBundle st :=
  hInv

theorem adapterReadMemory_error_unsupportedBinding_preserves_proofLayerInvariantBundle
    (contract : RuntimeBoundaryContract)
    (addr : SeLe4n.PAddr)
    (st : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (_hDeny : ¬ contract.memoryAccessAllowed st addr)
    (_hErr : adapterReadMemory contract addr st = .error (mapAdapterError .unsupportedBinding)) :
    proofLayerInvariantBundle st :=
  hInv

/-- WS-E3/H-07: Timer advancement preserves VSpace invariant bundle.
Timer-only state changes do not affect the object store or ASID table. -/
private theorem advanceTimerState_preserves_vspaceInvariantBundle
    (ticks : Nat) (st : SystemState)
    (hInv : vspaceInvariantBundle st) :
    vspaceInvariantBundle (advanceTimerState ticks st) := by
  rcases hInv with ⟨hUniq, hNonOverlap, hConsist, hWx, hBound, hCrossAsid, hCanonical⟩
  exact ⟨by exact hUniq, by exact hNonOverlap, by exact hConsist, by exact hWx, by exact hBound, by exact hCrossAsid, by exact hCanonical⟩

/-- WS-E3/H-07: Register writes preserve VSpace invariant bundle.
Register-only state changes do not affect the object store or ASID table. -/
private theorem writeRegisterState_preserves_vspaceInvariantBundle
    (reg : SeLe4n.RegName) (value : SeLe4n.RegValue) (st : SystemState)
    (hInv : vspaceInvariantBundle st) :
    vspaceInvariantBundle (writeRegisterState reg value st) := by
  rcases hInv with ⟨hUniq, hNonOverlap, hConsist, hWx, hBound, hCrossAsid, hCanonical⟩
  exact ⟨by exact hUniq, by exact hNonOverlap, by exact hConsist, by exact hWx, by exact hBound, by exact hCrossAsid, by exact hCanonical⟩

-- ============================================================================
-- X1-F/G: Context-switch atomic operation preserves proofLayerInvariantBundle
-- ============================================================================

/-- X1-G: Context-switch state preserves VSpace invariant bundle.
    Context switch only modifies `machine.regs` and `scheduler.current`,
    neither of which affects object store or ASID table. -/
private theorem contextSwitchState_preserves_vspaceInvariantBundle
    (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile) (st : SystemState)
    (hInv : vspaceInvariantBundle st) :
    vspaceInvariantBundle (contextSwitchState newTid newRegs st) := by
  rcases hInv with ⟨hUniq, hNonOverlap, hConsist, hWx, hBound, hCrossAsid, hCanonical⟩
  exact ⟨hUniq, hNonOverlap, hConsist, hWx, hBound, hCrossAsid, hCanonical⟩

/-- X1-G: Context-switch preserves `contextMatchesCurrent` when the loaded
    registers match the new thread's saved context.

    This is the core theorem that makes the atomic context-switch sound: by
    loading `tcb.registerContext` into `machine.regs` and setting
    `scheduler.current := some newTid` simultaneously, the register file
    equality `st'.machine.regs = tcb.registerContext` holds by construction. -/
theorem contextSwitchState_preserves_contextMatchesCurrent
    (st : SystemState) (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile)
    (tcb : TCB)
    (hLookup : st.objects[newTid.toObjId]? = some (.tcb tcb))
    (hRegs : newRegs = tcb.registerContext) :
    contextMatchesCurrent (contextSwitchState newTid newRegs st) := by
  simp [contextMatchesCurrent, contextSwitchState, hLookup, hRegs]
  exact RegisterFile.beq_self _

/-- X1-G: Context-switch preserves `currentThreadValid` when the target
    thread has a valid TCB in the object store. -/
theorem contextSwitchState_preserves_currentThreadValid
    (st : SystemState) (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile)
    (tcb : TCB)
    (hLookup : st.objects[newTid.toObjId]? = some (.tcb tcb)) :
    currentThreadValid (contextSwitchState newTid newRegs st) := by
  show currentThreadValid { st with machine := _, scheduler := _ }
  unfold currentThreadValid; simp; exact ⟨tcb, hLookup⟩

-- ============================================================================
-- L-06/WS-E3: Default SystemState initialization proofs
-- ============================================================================

/-- W6-E (L-11): Helper — the default state's objects table has no entries.
    Extracted to eliminate 24+ identical `RHTable_get?_empty 16 (by omega)` calls
    across the default-state proof section. All default-state proofs for
    object-quantified predicates follow the same pattern: assume an object exists,
    derive a contradiction from `default_objects_none`. -/
private theorem default_objects_none (oid : SeLe4n.ObjId) :
    (default : SystemState).objects[oid]? = none :=
  RHTable_get?_empty 16 (by omega)

/-- W6-E: Helper — vacuous discharge for default-state proofs. When a hypothesis
    `hObj : (default : SystemState).objects[oid]? = some _` is present, this
    derives a contradiction since the empty state has no objects. -/
private theorem default_objects_absurd {α : Prop} {oid : SeLe4n.ObjId} {v : KernelObject}
    (hObj : (default : SystemState).objects[oid]? = some v) : α := by
  rw [default_objects_none] at hObj; exact absurd hObj (by simp)

/-- L-06/WS-E3: The default (empty) `SystemState` satisfies the full composed
`proofLayerInvariantBundle`. This provides the base case for invariant induction:
the system starts in a valid state. All invariant components hold vacuously
because the empty state has no objects, no threads, no services, and an empty
scheduler. -/
private theorem default_schedulerInvariantBundle :
    schedulerInvariantBundle (default : SystemState) := by
  -- schedulerInvariantBundle = queueCurrentConsistent ∧ runQueueUnique ∧ currentThreadValid
  -- For default state: current = none, runnable = [], objects = none
  refine ⟨?_, ?_, ?_⟩
  · -- queueCurrentConsistent: current = none → True
    simp [queueCurrentConsistent]
  · -- runQueueUnique: [].Nodup
    exact List.nodup_nil
  · -- currentThreadValid: current = none → True
    simp [currentThreadValid]

private theorem default_ipcInvariant :
    ipcInvariant (default : SystemState) := by
  intro oid ntfn hObj; exact default_objects_absurd hObj

private theorem default_lifecycleInvariantBundle :
    lifecycleInvariantBundle (default : SystemState) :=
  lifecycleInvariantBundle_of_metadata_consistent _ default_systemState_lifecycleConsistent

private theorem default_ipcSchedulerContractPredicates :
    ipcSchedulerContractPredicates (default : SystemState) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tid tcb hObj; exact default_objects_absurd hObj
  · intro tid tcb eid hObj; exact default_objects_absurd hObj
  · intro tid tcb eid hObj; exact default_objects_absurd hObj
  · intro tid tcb eid hObj; exact default_objects_absurd hObj
  · intro tid tcb eid rt hObj; exact default_objects_absurd hObj
  · intro tid tcb nid hObj; exact default_objects_absurd hObj

/-- WS-H4 refactor: Extract default-state capabilityInvariantBundle construction
to eliminate 4x duplication in `default_system_state_proofLayerInvariantBundle`.
All components are vacuously true (empty objects/cdtNodeSlot) or use
`CapDerivationTree.empty_edgeWellFounded`. -/
private theorem default_capabilityInvariantBundle :
    capabilityInvariantBundle (default : SystemState) :=
  ⟨by intro oid cn hObj; exact default_objects_absurd hObj,
   by intro oid cn s c hObj; exact default_objects_absurd hObj,
   by intro oid cn hObj; exact default_objects_absurd hObj,
   by
    intro nodeId _ h
    have hempty : (default : SystemState).cdtNodeSlot[nodeId]? = none := by
      simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
    rw [hempty] at h; exact absurd h (by simp),
   by exact CapDerivationTree.empty_edgeWellFounded,
   by intro cnodeId cn hObj; exact default_objects_absurd hObj,
   by exact RHTable_empty_invExt 16 (by omega)⟩

-- WS-H12e: Default-state proofs for new invariant components

private theorem default_dualQueueSystemInvariant :
    dualQueueSystemInvariant (default : SystemState) := by
  refine ⟨?_, ?_, ?_⟩
  · intro epId ep hObj; exact default_objects_absurd hObj
  · constructor
    · intro a tcbA hObj; exact default_objects_absurd hObj
    · intro b tcbB hObj; exact default_objects_absurd hObj
  · intro tid hp
    exact match hp with
    | .single _ _ tcb hObj _ => by exact default_objects_absurd hObj
    | .cons _ _ _ tcb hObj _ _ => by exact default_objects_absurd hObj

private theorem default_allPendingMessagesBounded :
    allPendingMessagesBounded (default : SystemState) := by
  intro tid tcb msg hObj; exact default_objects_absurd hObj

private theorem default_badgeWellFormed :
    badgeWellFormed (default : SystemState) := by
  refine ⟨fun oid _ _ hObj => ?_, fun oid _ _ _ _ hObj => ?_⟩
  all_goals exact default_objects_absurd hObj

private theorem default_waitingThreadsPendingMessageNone :
    waitingThreadsPendingMessageNone (default : SystemState) := by
  intro tid tcb hObj; exact default_objects_absurd hObj

private theorem default_endpointQueueNoDup :
    endpointQueueNoDup (default : SystemState) := by
  intro oid ep hObj; exact default_objects_absurd hObj

private theorem default_ipcStateQueueMembershipConsistent :
    ipcStateQueueMembershipConsistent (default : SystemState) := by
  intro tid tcb hObj; exact default_objects_absurd hObj

private theorem default_queueNextBlockingConsistent :
    queueNextBlockingConsistent (default : SystemState) := by
  intro a b tcbA tcbB hA; exact default_objects_absurd hA

private theorem default_queueHeadBlockedConsistent :
    queueHeadBlockedConsistent (default : SystemState) := by
  intro epId ep hd tcb hEp; exact default_objects_absurd hEp

private theorem default_blockedThreadTimeoutConsistent :
    blockedThreadTimeoutConsistent (default : SystemState) := by
  intro tid tcb scId hObj; exact default_objects_absurd hObj

private theorem default_donationChainAcyclic :
    donationChainAcyclic (default : SystemState) := by
  intro _ _ _ _ _ _ h; exact default_objects_absurd h

private theorem default_donationOwnerValid :
    donationOwnerValid (default : SystemState) := by
  intro _ _ _ _ h; exact default_objects_absurd h

private theorem default_passiveServerIdle :
    passiveServerIdle (default : SystemState) := by
  intro _ _ h; exact default_objects_absurd h

private theorem default_donationBudgetTransfer :
    donationBudgetTransfer (default : SystemState) := by
  intro _ _ _ _ _ h; exact default_objects_absurd h

private theorem default_uniqueWaiters :
    uniqueWaiters (default : SystemState) := by
  intro _ _ h; exact default_objects_absurd h

private theorem default_blockedOnReplyHasTarget :
    blockedOnReplyHasTarget (default : SystemState) := by
  intro _ _ _ _ h; exact default_objects_absurd h

private theorem default_ipcInvariantFull :
    ipcInvariantFull (default : SystemState) :=
  ⟨default_ipcInvariant, default_dualQueueSystemInvariant, default_allPendingMessagesBounded,
   default_badgeWellFormed, default_waitingThreadsPendingMessageNone,
   default_endpointQueueNoDup, default_ipcStateQueueMembershipConsistent,
   default_queueNextBlockingConsistent, default_queueHeadBlockedConsistent,
   default_blockedThreadTimeoutConsistent,
   default_donationChainAcyclic, default_donationOwnerValid,
   default_passiveServerIdle, default_donationBudgetTransfer,
   default_uniqueWaiters,
   default_blockedOnReplyHasTarget⟩

private theorem default_contextMatchesCurrent :
    contextMatchesCurrent (default : SystemState) := by
  simp [contextMatchesCurrent]

private theorem default_currentThreadDequeueCoherent :
    currentThreadDequeueCoherent (default : SystemState) := by
  refine ⟨?_, ?_, ?_⟩
  · -- currentThreadIpcReady: current = none → True
    simp [currentThreadIpcReady]
  · -- currentNotEndpointQueueHead: current = none → True
    unfold currentNotEndpointQueueHead; simp
  · -- currentNotOnNotificationWaitList: current = none → True
    unfold currentNotOnNotificationWaitList; simp

private theorem default_schedulerInvariantBundleFull :
    schedulerInvariantBundleFull (default : SystemState) :=
  ⟨default_schedulerInvariantBundle,
   by
    unfold timeSlicePositive
    intro tid hMem
    have : (default : SystemState).scheduler.runnable = [] := by decide
    rw [this] at hMem; simp at hMem,
   by unfold currentTimeSlicePositive; simp,
   by unfold edfCurrentHasEarliestDeadline; simp,
   default_contextMatchesCurrent,
   default_runnableThreadsAreTCBs,
   by  -- R6-D: schedulerPriorityMatch — default runQueue empty, vacuously true
    intro tid hMem
    have hFlat : (default : SystemState).scheduler.runQueue.flat = [] := by decide
    have hInFlat := (RunQueue.mem_toList_iff_mem _ tid).mpr hMem
    simp [RunQueue.toList, hFlat] at hInFlat,
   by  -- V5-H: domainTimeRemainingPositive — default domainTimeRemaining is 5
    unfold domainTimeRemainingPositive; decide,
   default_domainScheduleEntriesPositive⟩

theorem default_system_state_proofLayerInvariantBundle :
    proofLayerInvariantBundle (default : SystemState) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. schedulerInvariantBundleFull (WS-H12e: now uses full bundle)
  · exact default_schedulerInvariantBundleFull
  -- 2. capabilityInvariantBundle (6-tuple: unique, sound, bounded, completeness, acyclicity, depth)
  · exact default_capabilityInvariantBundle
  -- 3. coreIpcInvariantBundle (WS-H12e: now uses ipcInvariantFull)
  · exact ⟨default_schedulerInvariantBundle, default_capabilityInvariantBundle, default_ipcInvariantFull⟩
  -- 4. ipcSchedulerCouplingInvariantBundle (WS-H12e: now includes contextMatchesCurrent + dequeueCoherent)
  · exact ⟨⟨default_schedulerInvariantBundle, default_capabilityInvariantBundle, default_ipcInvariantFull⟩,
           default_ipcSchedulerContractPredicates,
           default_contextMatchesCurrent,
           default_currentThreadDequeueCoherent⟩
  -- 5. lifecycleInvariantBundle
  · exact default_lifecycleInvariantBundle
  -- 6. serviceLifecycleCapabilityInvariantBundle = servicePolicySurface ∧ lifecycle ∧ capability ∧ registry
  · exact serviceLifecycleCapabilityInvariantBundle_of_components (default : SystemState)
      (by
        intro sid svc hSvc
        unfold lookupService at hSvc
        have hNone : (default : SystemState).services[sid]? = none := RHTable_get?_empty 16 (by omega)
        rw [hNone] at hSvc
        cases hSvc)
      default_lifecycleInvariantBundle
      default_capabilityInvariantBundle
      default_registryInvariant
  -- 7. vspaceInvariantBundle (7-conjunct: uniqueness ∧ nonOverlap ∧ asidTableConsistent ∧ wxExclusive ∧ boundedAddr ∧ crossAsidIsolation ∧ canonicalAddr)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro oid₁ oid₂ r₁ r₂ hObj₁; exact default_objects_absurd hObj₁
    · intro oid root hObj; exact default_objects_absurd hObj
    · constructor
      · intro asid oid hLookup; have h : (default : SystemState).asidTable[asid]? = none := RHTable_get?_empty 16 (by omega); rw [h] at hLookup; exact absurd hLookup (by simp)
      · intro oid root hObj; exact default_objects_absurd hObj
    · intro oid root v p perms hObj; exact default_objects_absurd hObj
    · intro oid root v p perms hObj; exact default_objects_absurd hObj
    · intro oidA oidB rA rB hObjA; exact default_objects_absurd hObjA
    · intro oid root v p perms hObj; exact default_objects_absurd hObj
  -- 8. crossSubsystemInvariant (R4-E + T5-J + Z9-D + AF1-B: 10 predicates)
  · exact default_crossSubsystemInvariant
  -- 9. tlbConsistent (R7-A.2/M-17: empty TLB is trivially consistent)
  · exact tlbConsistent_empty (default : SystemState)
  -- 10. schedulerInvariantBundleExtended (Z9-G: SchedContext invariants)
  · exact ⟨default_schedulerInvariantBundleFull,
           default_budgetPositive, default_currentBudgetPositive,
           default_schedContextsWellFormed, default_replenishQueueValid,
           default_schedContextBindingConsistent, default_effectiveParamsMatchRunQueue,
           default_boundThreadDomainConsistent⟩
  -- 11. notificationWaiterConsistent (AG7-D: empty objects → vacuous)
  · intro oid _ _ hObj; exact default_objects_absurd hObj

-- ============================================================================
-- M-08/WS-E6: Architecture assumption consumption bridge theorems
-- ============================================================================

/-! ## M-08/WS-E6: Assumption-to-proof consumption chain

The architecture assumptions in `Assumptions.lean` are structural declarations
that enumerate what the model expects from the hardware platform. The bridge
theorems below connect each assumption to the adapter preservation proofs
that actually *consume* it, closing the gap between "we declared it" and
"we use it in a proof."

### Assumption → Proof binding matrix

| Assumption | Consumed by | Evidence |
|---|---|---|
| `deterministicTimerProgress` | `adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle` | `AdapterProofHooks.preserveAdvanceTimer` requires `contract.timerMonotonic` |
| `deterministicRegisterContext` | `adapterWriteRegister_ok_preserves_proofLayerInvariantBundle` | `AdapterProofHooks.preserveWriteRegister` requires `contract.registerContextStable` |
| `memoryAccessSafety` | `adapterReadMemory_ok_preserves_proofLayerInvariantBundle` | `AdapterProofHooks.preserveReadMemory` requires `contract.memoryAccessAllowed` |
| `bootObjectTyping` | `default_system_state_proofLayerInvariantBundle` | Boot state satisfies lifecycle metadata consistency |
| `irqRoutingTotality` | IRQ handler lookup (structural) | All IRQs map to handler objects |
-/

/-- M-08/WS-E6: The `deterministicTimerProgress` assumption is consumed by
`adapterAdvanceTimer` through the `timerMonotonic` field of `RuntimeBoundaryContract`.
The adapter checks this contract at the timer-advance boundary and the
`AdapterProofHooks.preserveAdvanceTimer` field carries the proof obligation. -/
theorem deterministicTimerProgress_consumed_by_advanceTimer
    (contract : RuntimeBoundaryContract)
    (hooks : AdapterProofHooks contract)
    (ticks : Nat) (st : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (hMono : contract.timerMonotonic st (advanceTimerState ticks st))
    (hTicks : ticks ≠ 0) :
    proofLayerInvariantBundle (advanceTimerState ticks st) :=
  hooks.preserveAdvanceTimer ticks st hInv hMono hTicks

/-- M-08/WS-E6: The `deterministicRegisterContext` assumption is consumed by
`adapterWriteRegister` through the `registerContextStable` field of
`RuntimeBoundaryContract`. -/
theorem deterministicRegisterContext_consumed_by_writeRegister
    (contract : RuntimeBoundaryContract)
    (hooks : AdapterProofHooks contract)
    (reg : SeLe4n.RegName) (value : SeLe4n.RegValue) (st : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (hStable : contract.registerContextStable st (writeRegisterState reg value st)) :
    proofLayerInvariantBundle (writeRegisterState reg value st) :=
  hooks.preserveWriteRegister reg value st hInv hStable

/-- M-08/WS-E6: The `memoryAccessSafety` assumption is consumed by
`adapterReadMemory` through the `memoryAccessAllowed` field of
`RuntimeBoundaryContract`. Read operations are state-preserving, so the
pre-state invariant carries through directly. -/
theorem memoryAccessSafety_consumed_by_readMemory
    (contract : RuntimeBoundaryContract)
    (hooks : AdapterProofHooks contract)
    (addr : SeLe4n.PAddr) (st : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (hAllow : contract.memoryAccessAllowed st addr) :
    proofLayerInvariantBundle st :=
  hooks.preserveReadMemory addr st hInv hAllow

-- ============================================================================
-- WS-H15d/A-42: Generic adapter preservation lemmas
-- ============================================================================

/-! ## WS-H15d/A-42: Generic adapter preservation infrastructure

The adapter state transformations (`advanceTimerState`, `writeRegisterState`)
only modify `SystemState.machine` fields. The `proofLayerInvariantBundle`
components primarily examine `objects`, `scheduler`, `lifecycle`, `services`,
and `asidTable` — fields unchanged by machine-only modifications.

**Timer advancement** (`advanceTimerState`): modifies only `machine.timer`.
All 7 invariant-bundle components are trivially preserved because `machine.regs`,
`objects`, `scheduler`, etc. are definitionally unchanged.

**Memory read** (`preserveReadMemory`): state is unchanged. Trivially `id`.

**Register write** (`writeRegisterState`): modifies `machine.regs`. Six of the 7
bundle components are preserved (they don't inspect `machine.regs`). However,
`contextMatchesCurrent` (part of `schedulerInvariantBundleFull`) equates
`st.machine.regs` with the current thread's `tcb.registerContext`. Register
writes that change the register file can break this invariant.

Contracts with `registerContextStable := False` (e.g., simulation restrictive)
trivially satisfy the `preserveWriteRegister` obligation: the adapter rejects
all writes, so the proof follows from `False.elim`. Concrete proof hooks for
specific platforms are provided in `Platform/Sim/ProofHooks.lean`. -/

/-- WS-H15d/A-42: Timer advancement preserves the full `proofLayerInvariantBundle`.
Generic over any `RuntimeBoundaryContract` because `advanceTimerState` only
modifies `machine.timer`, leaving all invariant-relevant fields unchanged.
Lean can see through the record update `{ st with machine := { st.machine with timer := ... } }`
to verify that `scheduler`, `objects`, `machine.regs`, etc. are definitionally equal. -/
private theorem advanceTimerState_preserves_capabilityInvariantBundle
    (ticks : Nat) (st : SystemState)
    (hCap : capabilityInvariantBundle st) :
    capabilityInvariantBundle (advanceTimerState ticks st) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hCap
  exact ⟨by exact h1, by exact h2, by exact h3,
         by exact h4, by exact h5, by exact h6⟩

private theorem advanceTimerState_preserves_ipcInvariantFull
    (ticks : Nat) (st : SystemState)
    (hIpc : ipcInvariantFull st) :
    ipcInvariantFull (advanceTimerState ticks st) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hIpc
  have hObjs : (advanceTimerState ticks st).objects = st.objects := by
    unfold advanceTimerState; rfl
  have hLk : ∀ (x : SeLe4n.ObjId), (advanceTimerState ticks st).objects[x]? = st.objects[x]? := by
    intro x; exact congrArg (·.get? x) hObjs
  refine ⟨by exact h1, ?_, by exact h3, by exact h4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- dualQueueSystemInvariant
  · obtain ⟨hEp, hLink, hAcyc⟩ := h2
    refine ⟨fun epId ep hObj => hEp epId ep (hObjs ▸ hObj),
           ⟨fun a tcbA hA b hN => (hLink.1 a tcbA (hObjs ▸ hA) b hN).imp fun tcbB ⟨h1, h2⟩ => ⟨hObjs ▸ h1, h2⟩,
            fun b tcbB hB a hP => (hLink.2 b tcbB (hObjs ▸ hB) a hP).imp fun tcbA ⟨h1, h2⟩ => ⟨hObjs ▸ h1, h2⟩⟩,
           fun tid hp => hAcyc tid (transportPath hObjs hp)⟩
  -- waitingThreadsPendingMessageNone
  · intro tid tcb hObj; exact h5 tid tcb (hObjs ▸ hObj)
  -- endpointQueueNoDup
  · intro oid ep hObj; rw [hLk] at hObj; exact h6 oid ep hObj
  -- ipcStateQueueMembershipConsistent
  · exact ipcStateQueueMembershipConsistent_of_objects_eq st _ hLk h7
  -- queueNextBlockingConsistent
  · intro a b tcbA tcbB hA hB hN
    exact h8 a b tcbA tcbB (hObjs ▸ hA) (hObjs ▸ hB) hN
  -- queueHeadBlockedConsistent
  · intro epId ep hd tcb hEp hTcb
    exact h9 epId ep hd tcb (hObjs ▸ hEp) (hObjs ▸ hTcb)
  -- blockedThreadTimeoutConsistent
  · intro tid tcb scId hObj hTimeout
    exact h10 tid tcb scId (hObjs ▸ hObj) hTimeout
  -- Z7: donationChainAcyclic
  · intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1Obj h2Obj hB1 hB2
    exact h11 tid1 tid2 tcb1 tcb2 scId1 scId2 (hObjs ▸ h1Obj) (hObjs ▸ h2Obj) hB1 hB2
  -- Z7: donationOwnerValid
  · intro tid tcb scId owner hObj hBinding
    have ⟨hSc, hOwner⟩ := h12 tid tcb scId owner (hObjs ▸ hObj) hBinding
    exact ⟨hSc.imp fun sc hSc => hObjs ▸ hSc, hOwner.imp fun ownerTcb ⟨hO, hEp⟩ => ⟨hObjs ▸ hO, hEp⟩⟩
  -- Z7: passiveServerIdle
  · intro tid tcb hObj hUnbound hNotInRQ hNotCurr
    exact h13 tid tcb (hObjs ▸ hObj) hUnbound hNotInRQ hNotCurr
  -- Z7: donationBudgetTransfer
  · intro tid1 tid2 tcb1 tcb2 scId h1Obj h2Obj hNe hB1 hB2
    exact h14 tid1 tid2 tcb1 tcb2 scId (hObjs ▸ h1Obj) (hObjs ▸ h2Obj) hNe hB1 hB2
  -- AG1-C: uniqueWaiters
  · intro oid ntfn hObj; exact h15 oid ntfn (hObjs ▸ hObj)
  -- AJ1-B: blockedOnReplyHasTarget
  · intro tid tcb epId rt hObj hIpc; exact h16 tid tcb epId rt (hObjs ▸ hObj) hIpc
  where
    transportPath {a b : SeLe4n.ThreadId}
        (hObjs : (advanceTimerState ticks st).objects = st.objects)
        (hp : QueueNextPath (advanceTimerState ticks st) a b) :
        QueueNextPath st a b :=
      match hp with
      | .single _ _ tcb hObj hN => .single _ _ tcb (hObjs ▸ hObj) hN
      | .cons _ _ _ tcb hObj hN tail => .cons _ _ _ tcb (hObjs ▸ hObj) hN (transportPath hObjs tail)

/-- U4-G/U4-H: serviceEdge transfer — if two states have the same `services` field,
    a serviceEdge in one is a serviceEdge in the other. -/
private theorem serviceEdge_of_services_eq {st st' : SystemState}
    (hSvc : st'.services = st.services) {a b : ServiceId}
    (h : serviceEdge st' a b) : serviceEdge st a b := by
  obtain ⟨svc, hL, hM⟩ := h
  exact ⟨svc, by rw [lookupService, ← hSvc, ← lookupService]; exact hL, hM⟩

/-- U4-G/U4-H: serviceNontrivialPath transfer — same-services states have identical paths. -/
private theorem serviceNontrivialPath_of_services_eq {st st' : SystemState}
    (hSvc : st'.services = st.services) {a b : ServiceId}
    (h : serviceNontrivialPath st' a b) : serviceNontrivialPath st a b := by
  induction h with
  | single hedge => exact .single (serviceEdge_of_services_eq hSvc hedge)
  | cons hedge _ ih => exact .cons (serviceEdge_of_services_eq hSvc hedge) ih

/-- U4-G/U4-H: advanceTimerState preserves serviceGraphInvariant.
    advanceTimerState only modifies machine.timer; services and objects are unchanged. -/
private theorem advanceTimerState_preserves_serviceGraphInvariant
    (ticks : Nat) (st : SystemState)
    (h : serviceGraphInvariant st) :
    serviceGraphInvariant (advanceTimerState ticks st) := by
  obtain ⟨hAcyc, hBound⟩ := h
  have hSvcEq : (advanceTimerState ticks st).services = st.services := rfl
  constructor
  · -- serviceDependencyAcyclic
    intro a hPath
    exact hAcyc a (serviceNontrivialPath_of_services_eq hSvcEq hPath)
  · -- serviceCountBounded: depends on services + objectIndex, both unchanged
    -- Since advanceTimerState only touches machine.timer, the serviceCountBounded
    -- proposition is definitionally equal between the two states
    exact hBound

theorem advanceTimerState_preserves_proofLayerInvariantBundle
    (ticks : Nat) (st : SystemState)
    (hInv : proofLayerInvariantBundle st) :
    proofLayerInvariantBundle (advanceTimerState ticks st) := by
  obtain ⟨hSched, hCap, hIpc, hCoupling, hLife, hSvc, hVsp, hCross, hTlb, hExt, hNWC⟩ := hInv
  refine ⟨by exact hSched,
         advanceTimerState_preserves_capabilityInvariantBundle ticks st hCap,
         ?_, ?_, by exact hLife, ?_, ?_, ?_, by exact hTlb, by exact hExt, by exact hNWC⟩
  -- coreIpcInvariantBundle
  · obtain ⟨hS, hC, hI⟩ := hIpc
    exact ⟨by exact hS,
           advanceTimerState_preserves_capabilityInvariantBundle ticks st hC,
           advanceTimerState_preserves_ipcInvariantFull ticks st hI⟩
  -- ipcSchedulerCouplingInvariantBundle
  · obtain ⟨⟨hS, hC, hI⟩, hCoh, hCtx, hDeq⟩ := hCoupling
    exact ⟨⟨by exact hS,
            advanceTimerState_preserves_capabilityInvariantBundle ticks st hC,
            advanceTimerState_preserves_ipcInvariantFull ticks st hI⟩,
           by exact hCoh, by exact hCtx, by exact hDeq⟩
  -- serviceLifecycleCapabilityInvariantBundle
  · obtain ⟨hP, hL, hC, hR⟩ := hSvc
    exact ⟨by exact hP, by exact hL,
           advanceTimerState_preserves_capabilityInvariantBundle ticks st hC,
           by exact hR⟩
  -- vspaceInvariantBundle
  · exact advanceTimerState_preserves_vspaceInvariantBundle ticks st hVsp
  -- crossSubsystemInvariant (T5-J + U4-G + Z9-D + AE5-C + AF1-B + AM4-A: 11 conjuncts)
  · obtain ⟨h1, h1i, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hCross
    refine ⟨h1, h1i, h2, h3, h4, advanceTimerState_preserves_serviceGraphInvariant ticks st h5,
           h6, h7, h8,
           PriorityInheritance.blockingAcyclic_frame st (advanceTimerState ticks st) h9
             (fun _ => by simp [PriorityInheritance.blockingServer, advanceTimerState])
             (by simp [advanceTimerState]), ?_⟩
    -- AM4-A: advanceTimerState preserves both `objects` and `lifecycle.objectTypes`,
    -- so the lockstep invariant transports unchanged.
    intro oid obj hObj'
    have hObjEq : (advanceTimerState ticks st).objects = st.objects := by
      simp [advanceTimerState]
    have hTyEq : (advanceTimerState ticks st).lifecycle.objectTypes
        = st.lifecycle.objectTypes := by
      simp [advanceTimerState]
    rw [hObjEq] at hObj'
    rw [hTyEq]
    exact h10 oid obj hObj'

-- ============================================================================
-- AG7-D: writeRegisterState preserves proofLayerInvariantBundle
-- ============================================================================

private theorem writeRegisterState_preserves_capabilityInvariantBundle
    (reg : SeLe4n.RegName) (value : SeLe4n.RegValue) (st : SystemState)
    (hCap : capabilityInvariantBundle st) :
    capabilityInvariantBundle (writeRegisterState reg value st) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hCap
  exact ⟨by exact h1, by exact h2, by exact h3,
         by exact h4, by exact h5, by exact h6⟩

private theorem writeRegisterState_preserves_ipcInvariantFull
    (reg : SeLe4n.RegName) (value : SeLe4n.RegValue) (st : SystemState)
    (hIpc : ipcInvariantFull st) :
    ipcInvariantFull (writeRegisterState reg value st) := by
  have hObjs : (writeRegisterState reg value st).objects = st.objects := rfl
  have hLk : ∀ (x : SeLe4n.ObjId),
      (writeRegisterState reg value st).objects[x]? = st.objects[x]? := fun x => congrArg (·.get? x) hObjs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hIpc
  refine ⟨by exact h1, ?_, by exact h3, by exact h4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hEp, hLink, hAcyc⟩ := h2
    exact ⟨fun epId ep hObj => hEp epId ep (hObjs ▸ hObj),
           ⟨fun a tcbA hA b hN => (hLink.1 a tcbA (hObjs ▸ hA) b hN).imp
              fun tcbB ⟨h1, h2⟩ => ⟨hObjs ▸ h1, h2⟩,
            fun b tcbB hB a hP => (hLink.2 b tcbB (hObjs ▸ hB) a hP).imp
              fun tcbA ⟨h1, h2⟩ => ⟨hObjs ▸ h1, h2⟩⟩,
           fun tid hp => hAcyc tid (writeRegState_transportPath hObjs hp)⟩
  · intro tid tcb hObj; exact h5 tid tcb (hObjs ▸ hObj)
  · intro oid ep hObj; rw [hLk] at hObj; exact h6 oid ep hObj
  · exact ipcStateQueueMembershipConsistent_of_objects_eq st _ hLk h7
  · intro a b tcbA tcbB hA hB hN; exact h8 a b tcbA tcbB (hObjs ▸ hA) (hObjs ▸ hB) hN
  · intro epId ep hd tcb hEp hTcb; exact h9 epId ep hd tcb (hObjs ▸ hEp) (hObjs ▸ hTcb)
  · intro tid tcb scId hObj hTimeout; exact h10 tid tcb scId (hObjs ▸ hObj) hTimeout
  · intro t1 t2 tc1 tc2 s1 s2 h1O h2O hB1 hB2
    exact h11 t1 t2 tc1 tc2 s1 s2 (hObjs ▸ h1O) (hObjs ▸ h2O) hB1 hB2
  · intro tid tcb scId owner hObj hBinding
    have ⟨hSc, hOwner⟩ := h12 tid tcb scId owner (hObjs ▸ hObj) hBinding
    exact ⟨hSc.imp fun sc hSc => hObjs ▸ hSc, hOwner.imp fun ownerTcb ⟨hO, hEp⟩ => ⟨hObjs ▸ hO, hEp⟩⟩
  · intro tid tcb hObj hUnbound hNotInRQ hNotCurr; exact h13 tid tcb (hObjs ▸ hObj) hUnbound hNotInRQ hNotCurr
  · intro t1 t2 tc1 tc2 scId h1O h2O hNe hB1 hB2
    exact h14 t1 t2 tc1 tc2 scId (hObjs ▸ h1O) (hObjs ▸ h2O) hNe hB1 hB2
  · intro oid ntfn hObj; exact h15 oid ntfn (hObjs ▸ hObj)
  -- AJ1-B: blockedOnReplyHasTarget
  · intro tid tcb epId rt hObj hIpc; exact h16 tid tcb epId rt (hObjs ▸ hObj) hIpc
  where
    writeRegState_transportPath {a b : SeLe4n.ThreadId}
        (hObjs : (writeRegisterState reg value st).objects = st.objects)
        (hp : QueueNextPath (writeRegisterState reg value st) a b) :
        QueueNextPath st a b :=
      match hp with
      | .single _ _ tcb hObj hN => .single _ _ tcb (hObjs ▸ hObj) hN
      | .cons _ _ _ tcb hObj hN tail => .cons _ _ _ tcb (hObjs ▸ hObj) hN (writeRegState_transportPath hObjs tail)

/-- AG7-D: Register writes preserve the full `proofLayerInvariantBundle` when
    `contextMatchesCurrent` holds for the post-state.

    `writeRegisterState` only modifies `machine.regs`. All other system state
    fields (objects, scheduler, services, lifecycle, etc.) are definitionally
    unchanged. The only non-trivial predicate is `contextMatchesCurrent`, which
    compares `machine.regs` with the current TCB's `registerContext`. This is
    provided as a hypothesis — the RPi5 production contract validates it via
    `registerContextStablePred`. -/
theorem writeRegisterState_preserves_proofLayerInvariantBundle
    (reg : SeLe4n.RegName) (value : SeLe4n.RegValue) (st : SystemState)
    (hInv : proofLayerInvariantBundle st)
    (hCtx : contextMatchesCurrent (writeRegisterState reg value st)) :
    proofLayerInvariantBundle (writeRegisterState reg value st) := by
  obtain ⟨hSched, hCap, hIpc, hCoupling, hLife, hSvc, hVsp, hCross, hTlb, hExt, hNWC⟩ := hInv
  -- writeRegisterState only changes machine.regs — establish definitional equalities
  have hEq : writeRegisterState reg value st =
      { st with machine := { st.machine with regs := SeLe4n.writeReg st.machine.regs reg value } } :=
    rfl
  -- Most predicates transfer via `by exact` since objects/scheduler/services are unchanged
  -- at the struct level; others need the rewrite for Lean to see through the record update
  refine ⟨?_, ?_, ?_, ?_, by exact hLife, ?_,
         writeRegisterState_preserves_vspaceInvariantBundle reg value st hVsp,
         ?_, by exact hTlb, ?_, by exact hNWC⟩
  -- schedulerInvariantBundleFull: swap contextMatchesCurrent
  · obtain ⟨hBase, hTs, hCts, hEdf, _, hRunn, hPri, hDom, hDomE⟩ := hSched
    exact ⟨hBase, hTs, hCts, hEdf, hCtx, hRunn, hPri, hDom, hDomE⟩
  -- capabilityInvariantBundle
  · exact writeRegisterState_preserves_capabilityInvariantBundle reg value st hCap
  -- coreIpcInvariantBundle
  · obtain ⟨hS, hC, hI⟩ := hIpc
    exact ⟨by exact hS,
           writeRegisterState_preserves_capabilityInvariantBundle reg value st hC,
           writeRegisterState_preserves_ipcInvariantFull reg value st hI⟩
  -- ipcSchedulerCouplingInvariantBundle: swap contextMatchesCurrent
  · obtain ⟨⟨hS, hC, hI⟩, hCoh, _, hDeq⟩ := hCoupling
    exact ⟨⟨by exact hS,
            writeRegisterState_preserves_capabilityInvariantBundle reg value st hC,
            writeRegisterState_preserves_ipcInvariantFull reg value st hI⟩,
           by exact hCoh, hCtx, by exact hDeq⟩
  -- serviceLifecycleCapabilityInvariantBundle
  · obtain ⟨hP, hL, hC, hR⟩ := hSvc
    exact ⟨by exact hP, by exact hL,
           writeRegisterState_preserves_capabilityInvariantBundle reg value st hC,
           by exact hR⟩
  -- crossSubsystemInvariant: objects/scheduler/services unchanged (AM4-A: 11 conjuncts)
  · obtain ⟨h1, h1i, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hCross
    have hSvcEq : (writeRegisterState reg value st).services = st.services := rfl
    refine ⟨by exact h1, by exact h1i, by exact h2, by exact h3, by exact h4, ?_,
           by exact h6, by exact h7, by exact h8, ?_, ?_⟩
    -- serviceGraphInvariant
    · obtain ⟨hAcyc, hBound⟩ := h5
      exact ⟨fun a hPath => hAcyc a (serviceNontrivialPath_of_services_eq hSvcEq hPath),
             hBound⟩
    -- blockingAcyclic
    · exact PriorityInheritance.blockingAcyclic_frame st (writeRegisterState reg value st) h9
        (fun _ => by simp [PriorityInheritance.blockingServer, writeRegisterState])
        (by simp [writeRegisterState])
    -- AM4-A: lifecycleObjectTypeLockstep — writeRegisterState leaves
    -- objects and lifecycle.objectTypes unchanged.
    · intro oid obj hObj'
      have hObjEq : (writeRegisterState reg value st).objects = st.objects := rfl
      have hTyEq : (writeRegisterState reg value st).lifecycle.objectTypes
          = st.lifecycle.objectTypes := rfl
      rw [hObjEq] at hObj'
      rw [hTyEq]
      exact h10 oid obj hObj'
  -- schedulerInvariantBundleExtended: swap contextMatchesCurrent in inner Full
  · obtain ⟨⟨hBase, hTs, hCts, hEdf, _, hRunn, hPri, hDom, hDomE⟩,
            hBud, hCBud, hWf, hRq, hBind, hEff, hBound⟩ := hExt
    exact ⟨⟨by exact hBase, by exact hTs, by exact hCts, by exact hEdf, hCtx,
            by exact hRunn, by exact hPri, by exact hDom, by exact hDomE⟩,
           by exact hBud, by exact hCBud, by exact hWf, by exact hRq,
           by exact hBind, by exact hEff, by exact hBound⟩

-- ============================================================================
-- AG7-D: contextSwitchState helpers
-- ============================================================================

/-- AG7-D: `ipcInvariantFull` is preserved through `contextSwitchState`.
    All 16 conjuncts depend only on `st.objects` except `passiveServerIdle`
    which also references `scheduler.current` and `scheduler.runQueue`.
    `passiveServerIdle` transfers because the old current thread (if any) has
    `ipcState = .ready` (from `currentThreadIpcReady`), satisfying the
    conclusion directly. -/
private theorem contextSwitchState_preserves_ipcInvariantFull
    (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile) (st : SystemState)
    (hIpc : ipcInvariantFull st)
    (hCurIpc : currentThreadIpcReady st) :
    ipcInvariantFull (contextSwitchState newTid newRegs st) := by
  have hObjs : (contextSwitchState newTid newRegs st).objects = st.objects := rfl
  have hLk : ∀ (x : SeLe4n.ObjId),
      (contextSwitchState newTid newRegs st).objects[x]? = st.objects[x]? :=
    fun x => congrArg (·.get? x) hObjs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hIpc
  refine ⟨by exact h1, ?_, by exact h3, by exact h4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hEp, hLink, hAcyc⟩ := h2
    exact ⟨fun epId ep hObj => hEp epId ep (hObjs ▸ hObj),
           ⟨fun a tcbA hA b hN => (hLink.1 a tcbA (hObjs ▸ hA) b hN).imp
              fun tcbB ⟨h1, h2⟩ => ⟨hObjs ▸ h1, h2⟩,
            fun b tcbB hB a hP => (hLink.2 b tcbB (hObjs ▸ hB) a hP).imp
              fun tcbA ⟨h1, h2⟩ => ⟨hObjs ▸ h1, h2⟩⟩,
           fun tid hp => hAcyc tid (ctxSwitch_transportPath hObjs hp)⟩
  · intro tid tcb hObj; exact h5 tid tcb (hObjs ▸ hObj)
  · intro oid ep hObj; rw [hLk] at hObj; exact h6 oid ep hObj
  · exact ipcStateQueueMembershipConsistent_of_objects_eq st _ hLk h7
  · intro a b tcbA tcbB hA hB hN; exact h8 a b tcbA tcbB (hObjs ▸ hA) (hObjs ▸ hB) hN
  · intro epId ep hd tcb hEp hTcb; exact h9 epId ep hd tcb (hObjs ▸ hEp) (hObjs ▸ hTcb)
  · intro tid tcb scId hObj hTimeout; exact h10 tid tcb scId (hObjs ▸ hObj) hTimeout
  · intro t1 t2 tc1 tc2 s1 s2 h1O h2O hB1 hB2
    exact h11 t1 t2 tc1 tc2 s1 s2 (hObjs ▸ h1O) (hObjs ▸ h2O) hB1 hB2
  · intro tid tcb scId owner hObj hBinding
    have ⟨hSc, hOwner⟩ := h12 tid tcb scId owner (hObjs ▸ hObj) hBinding
    exact ⟨hSc.imp fun sc hSc => hObjs ▸ hSc,
           hOwner.imp fun ownerTcb ⟨hO, hEp⟩ => ⟨hObjs ▸ hO, hEp⟩⟩
  -- passiveServerIdle: scheduler.current changes from old to some newTid
  · intro tid tcb hObj hUnbound hNotInRQ hNotCurr
    -- hNotCurr : (contextSwitchState ...).scheduler.current ≠ some tid
    -- i.e., some newTid ≠ some tid
    -- Case split on whether tid was the old current thread
    by_cases hOld : st.scheduler.current = some tid
    · -- tid was old current; currentThreadIpcReady gives ipcState = .ready
      simp [currentThreadIpcReady, hOld] at hCurIpc
      exact Or.inl (hCurIpc tcb (hObjs ▸ hObj))
    · -- tid was not old current; transfer from pre-state passiveServerIdle
      exact h13 tid tcb (hObjs ▸ hObj) hUnbound hNotInRQ hOld
  · intro t1 t2 tc1 tc2 scId h1O h2O hNe hB1 hB2
    exact h14 t1 t2 tc1 tc2 scId (hObjs ▸ h1O) (hObjs ▸ h2O) hNe hB1 hB2
  · intro oid ntfn hObj; exact h15 oid ntfn (hObjs ▸ hObj)
  -- AJ1-B: blockedOnReplyHasTarget
  · intro tid tcb epId rt hObj hIpc'; exact h16 tid tcb epId rt (hObjs ▸ hObj) hIpc'
  where
    ctxSwitch_transportPath {a b : SeLe4n.ThreadId}
        (hObjs : (contextSwitchState newTid newRegs st).objects = st.objects)
        (hp : QueueNextPath (contextSwitchState newTid newRegs st) a b) :
        QueueNextPath st a b :=
      match hp with
      | .single _ _ tcb hObj hN => .single _ _ tcb (hObjs ▸ hObj) hN
      | .cons _ _ _ tcb hObj hN tail =>
        .cons _ _ _ tcb (hObjs ▸ hObj) hN (ctxSwitch_transportPath hObjs tail)

-- ============================================================================
-- AG7-D: contextSwitchState preserves proofLayerInvariantBundle
-- ============================================================================

/-- AG7-D: Context switch preserves the full `proofLayerInvariantBundle` when
    the target thread satisfies all current-thread predicates.

    `contextSwitchState` atomically sets `scheduler.current := some newTid`
    and `machine.regs := newRegs`. All other fields (objects, runnable queue,
    services, lifecycle, etc.) are unchanged. Current-thread-dependent predicates
    are re-established from the explicit hypotheses; all other predicates are
    preserved by frame reasoning (unchanged fields).

    The hypotheses correspond to what the RPi5 production runtime contract
    (`registerContextStableCheck`) validates:
    1. TCB lookup for the new thread
    2. Register match (newRegs = tcb.registerContext)
    3. Not in runnable queue (dequeue-on-dispatch)
    4. Time-slice positivity
    5. IPC readiness (ipcState = .ready)
    6. EDF compatibility (deadline = 0)
    7. Budget sufficiency -/
theorem contextSwitchState_preserves_proofLayerInvariantBundle
    (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile) (st : SystemState)
    (tcb : TCB)
    (hInv : proofLayerInvariantBundle st)
    (hLookup : st.objects[newTid.toObjId]? = some (.tcb tcb))
    (hRegs : (newRegs == tcb.registerContext) = true)
    (hNotRunnable : newTid ∉ st.scheduler.runnable)
    (hTimeSlice : tcb.timeSlice > 0)
    (hIpcReady : tcb.ipcState = .ready)
    (hDeadline : tcb.deadline.toNat = 0)
    (hBudgetPost : currentBudgetPositive (contextSwitchState newTid newRegs st)) :
    proofLayerInvariantBundle (contextSwitchState newTid newRegs st) := by
  obtain ⟨hSched, hCap, hIpc, hCoupling, hLife, hSvc, hVsp, hCross, hTlb, hExt, hNWC⟩ := hInv
  -- contextSwitchState changes machine.regs and scheduler.current; objects unchanged
  have hObjs : (contextSwitchState newTid newRegs st).objects = st.objects := rfl
  -- Extract currentThreadIpcReady from the coupling bundle (needed for passiveServerIdle)
  have hCurIpcReady : currentThreadIpcReady st := hCoupling.2.2.2.1
  -- contextMatchesCurrent for the post-state: directly from BEq hypothesis
  have hCtxPost : contextMatchesCurrent (contextSwitchState newTid newRegs st) := by
    simp [contextMatchesCurrent, contextSwitchState, hLookup]; exact hRegs
  -- currentThreadValid for the post-state
  have hValidPost : currentThreadValid (contextSwitchState newTid newRegs st) :=
    contextSwitchState_preserves_currentThreadValid st newTid newRegs tcb hLookup
  -- currentNotEndpointQueueHead: ipcState = .ready contradicts queueHeadBlockedConsistent
  have hIpcFull := hIpc.2.2
  have hQHBC : queueHeadBlockedConsistent st := hIpcFull.2.2.2.2.2.2.2.2.1
  have hNotEpHead : currentNotEndpointQueueHead (contextSwitchState newTid newRegs st) := by
    show currentNotEndpointQueueHead { st with machine := _, scheduler := _ }
    unfold currentNotEndpointQueueHead; simp
    intro oid ep hObj
    have ⟨hRecv, hSend⟩ := hQHBC oid ep newTid tcb hObj hLookup
    constructor
    · intro hH; have := hRecv hH; rw [hIpcReady] at this; exact absurd this (by simp)
    · intro hH; have := hSend hH
      rcases this with h | h <;> { rw [hIpcReady] at h; exact absurd h (by simp) }
  -- currentNotOnNotificationWaitList: ipcState = .ready + notificationWaiterConsistent
  have hNotNtfnWait : currentNotOnNotificationWaitList
      (contextSwitchState newTid newRegs st) := by
    show currentNotOnNotificationWaitList { st with machine := _, scheduler := _ }
    unfold currentNotOnNotificationWaitList; simp
    intro oid ntfn hObj
    exact not_mem_waitingThreads_of_ipcState_ne st oid ntfn newTid tcb hNWC hObj hLookup
      (by rw [hIpcReady]; simp)
  -- currentThreadIpcReady for the post-state
  have hIpcReadyPost : currentThreadIpcReady (contextSwitchState newTid newRegs st) := by
    show currentThreadIpcReady { st with machine := _, scheduler := _ }
    unfold currentThreadIpcReady; simp
    intro tcb' hTcb'; rw [hLookup] at hTcb'; cases hTcb'; exact hIpcReady
  -- currentTimeSlicePositive for the post-state
  have hTsPost : currentTimeSlicePositive (contextSwitchState newTid newRegs st) := by
    show currentTimeSlicePositive { st with machine := _, scheduler := _ }
    unfold currentTimeSlicePositive; simp; rw [hLookup]; exact hTimeSlice
  -- edfCurrentHasEarliestDeadline: deadline = 0 → trivially satisfied
  have hEdfPost : edfCurrentHasEarliestDeadline (contextSwitchState newTid newRegs st) := by
    show edfCurrentHasEarliestDeadline { st with machine := _, scheduler := _ }
    unfold edfCurrentHasEarliestDeadline; simp; rw [hLookup]
    intro tid _
    cases h : st.objects[tid.toObjId]? with
    | none => trivial
    | some obj =>
      cases obj with
      | tcb _ => intro _ _ _; left; exact hDeadline
      | _ => trivial
  -- Compose the 11-tuple
  refine ⟨?_, ?_, ?_, ?_, by exact hLife, ?_,
         contextSwitchState_preserves_vspaceInvariantBundle newTid newRegs st hVsp,
         ?_, by exact hTlb, ?_, ?_⟩
  -- 1. schedulerInvariantBundleFull
  · obtain ⟨⟨_, hUniq, _⟩, hTs, _, _, _, hRunn, hPri, hDom, hDomE⟩ := hSched
    have hQCC : queueCurrentConsistent
        { st.scheduler with current := some newTid } := by
      unfold queueCurrentConsistent; simp; exact hNotRunnable
    exact ⟨⟨hQCC, hUniq, hValidPost⟩,
           hTs, hTsPost, hEdfPost, hCtxPost, hRunn, hPri, hDom, hDomE⟩
  -- 2. capabilityInvariantBundle: objects unchanged
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hCap
    exact ⟨by exact h1, by exact h2, by exact h3, by exact h4, by exact h5, by exact h6⟩
  -- 3. coreIpcInvariantBundle: scheduler base + cap + ipcFull preserved
  · obtain ⟨⟨_, hUniq, _⟩, hC, hI⟩ := hIpc
    have hQCC : queueCurrentConsistent
        { st.scheduler with current := some newTid } := by
      unfold queueCurrentConsistent; simp; exact hNotRunnable
    exact ⟨⟨hQCC, hUniq, hValidPost⟩, hC,
           contextSwitchState_preserves_ipcInvariantFull newTid newRegs st hI hCurIpcReady⟩
  -- 4. ipcSchedulerCouplingInvariantBundle: rebuild with new current-thread predicates
  · obtain ⟨⟨⟨_, hUniq, _⟩, hC, hI⟩, hCoh, _, _⟩ := hCoupling
    have hQCC : queueCurrentConsistent
        { st.scheduler with current := some newTid } := by
      unfold queueCurrentConsistent; simp; exact hNotRunnable
    exact ⟨⟨⟨hQCC, hUniq, hValidPost⟩, hC,
            contextSwitchState_preserves_ipcInvariantFull newTid newRegs st hI hCurIpcReady⟩,
           hCoh, hCtxPost, ⟨hIpcReadyPost, hNotEpHead, hNotNtfnWait⟩⟩
  -- 6. serviceLifecycleCapabilityInvariantBundle
  · obtain ⟨hP, hL, hC, hR⟩ := hSvc
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hC
    exact ⟨by exact hP, by exact hL,
           ⟨by exact h1, by exact h2, by exact h3, by exact h4, by exact h5, by exact h6⟩,
           by exact hR⟩
  -- 8. crossSubsystemInvariant: objects/services/serviceRegistry unchanged (AM4-A: 11 conjuncts)
  · obtain ⟨h1, h1i, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hCross
    have hSvcEq : (contextSwitchState newTid newRegs st).services = st.services := rfl
    refine ⟨by exact h1, by exact h1i, by exact h2, by exact h3, by exact h4, ?_,
           by exact h6, by exact h7, by exact h8, ?_, ?_⟩
    -- serviceGraphInvariant
    · obtain ⟨hAcyc, hBound⟩ := h5
      exact ⟨fun a hPath => hAcyc a (serviceNontrivialPath_of_services_eq hSvcEq hPath),
             hBound⟩
    -- blockingAcyclic
    · exact PriorityInheritance.blockingAcyclic_frame st (contextSwitchState newTid newRegs st) h9
        (fun _ => by simp [PriorityInheritance.blockingServer, contextSwitchState])
        (by simp [contextSwitchState])
    -- AM4-A: lifecycleObjectTypeLockstep
    · intro oid obj hObj'
      have hObjEq : (contextSwitchState newTid newRegs st).objects = st.objects := rfl
      have hTyEq : (contextSwitchState newTid newRegs st).lifecycle.objectTypes
          = st.lifecycle.objectTypes := rfl
      rw [hObjEq] at hObj'
      rw [hTyEq]
      exact h10 oid obj hObj'
  -- 10. schedulerInvariantBundleExtended: rebuild with new current-thread predicates
  · obtain ⟨hFull, hBud, _, hWf, hRq, hBind, hEff, hBound⟩ := hExt
    obtain ⟨⟨_, hUniq, _⟩, hTs, _, _, _, hRunn, hPri, hDom, hDomE⟩ := hFull
    have hQCC : queueCurrentConsistent
        { st.scheduler with current := some newTid } := by
      unfold queueCurrentConsistent; simp; exact hNotRunnable
    exact ⟨⟨⟨hQCC, hUniq, hValidPost⟩,
            hTs, hTsPost, hEdfPost, hCtxPost, hRunn, hPri, hDom, hDomE⟩,
           hBud, hBudgetPost, hWf, hRq, hBind, hEff, hBound⟩
  -- 11. notificationWaiterConsistent: objects unchanged
  · exact hNWC

-- ============================================================================
-- WS-J1-D: Register decode consistency predicate
-- ============================================================================

/-! ## WS-J1-D: Register Decode Consistency

The `registerDecodeConsistent` predicate asserts that whenever the current
thread's register file decodes successfully via `decodeSyscallArgs`, the
resulting typed references index valid kernel state:

1. The current thread (if any) has a valid TCB with a saved register context.
2. If the decode produces a `SyscallDecodeResult`, the `capAddr` field is
   a well-formed capability pointer (trivially true since CPtr is unbounded).
3. The `syscallId` maps to a defined access right (total by `syscallRequiredRight_total`).

This predicate bridges the decode layer and the kernel object store: raw
register values that produce typed references must correspond to objects
that the invariant bundle already governs.

Note: `registerDecodeConsistent` is intentionally *not* added as a conjunct
of `proofLayerInvariantBundle`. The predicate characterizes a property of the
decode path (a pure function over the register file), not a state invariant
over kernel objects. It is preserved trivially by all operations that do not
modify the current thread's register context, and substantively by context
switch operations that maintain `contextMatchesCurrent`. The predicate is
stated separately for composability with `syscallEntry` soundness theorems. -/

/-- WS-J1-D: Register decode consistency — if the current thread has a TCB,
its register context is available for syscall decode. This is the bridge
between `contextMatchesCurrent` (scheduler invariant) and the decode layer. -/
def registerDecodeConsistent (st : SystemState) : Prop :=
  ∀ tid, st.scheduler.current = some tid →
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb)

/-- WS-J1-D: The default (empty) system state satisfies `registerDecodeConsistent`
vacuously — there is no current thread. -/
theorem default_registerDecodeConsistent :
    registerDecodeConsistent (default : SystemState) := by
  intro tid hCur; simp at hCur

/-- WS-J1-D: `registerDecodeConsistent` is implied by `schedulerInvariantBundleFull`,
which includes `currentThreadValid`. This bridges the existing scheduler invariant
surface with the decode layer without adding a new conjunct to `proofLayerInvariantBundle`. -/
theorem registerDecodeConsistent_of_proofLayerInvariantBundle
    (st : SystemState)
    (hInv : proofLayerInvariantBundle st) :
    registerDecodeConsistent st := by
  intro tid hCur
  obtain ⟨hSchedFull, _⟩ := hInv
  obtain ⟨⟨_, _, hValid⟩, _⟩ := hSchedFull
  -- currentThreadValid matches on scheduler.current; unfold and substitute
  unfold currentThreadValid at hValid
  rw [hCur] at hValid
  exact hValid

/-- WS-J1-D: Timer advancement preserves `registerDecodeConsistent`.
Timer-only state changes do not affect the object store or scheduler current. -/
theorem advanceTimerState_preserves_registerDecodeConsistent
    (ticks : Nat) (st : SystemState)
    (hRdc : registerDecodeConsistent st) :
    registerDecodeConsistent (advanceTimerState ticks st) := by
  intro tid hCur; exact hRdc tid hCur

/-- WS-J1-D: Register writes preserve `registerDecodeConsistent`.
Register-only state changes do not affect the object store or scheduler current. -/
theorem writeRegisterState_preserves_registerDecodeConsistent
    (reg : SeLe4n.RegName) (value : SeLe4n.RegValue) (st : SystemState)
    (hRdc : registerDecodeConsistent st) :
    registerDecodeConsistent (writeRegisterState reg value st) := by
  intro tid hCur; exact hRdc tid hCur

end SeLe4n.Kernel.Architecture
