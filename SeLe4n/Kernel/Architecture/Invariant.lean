/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.Adapter
import SeLe4n.Kernel.Architecture.VSpaceInvariant
import SeLe4n.Kernel.Service.Invariant

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
| **Substantive preservation** | `adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle`, `adapterWriteRegister_ok_preserves_proofLayerInvariantBundle`, `adapterReadMemory_ok_preserves_proofLayerInvariantBundle` |
| **Error-case preservation** | `adapterAdvanceTimer_error_invalidContext_preserves_proofLayerInvariantBundle`, `adapterAdvanceTimer_error_unsupportedBinding_preserves_proofLayerInvariantBundle`, `adapterWriteRegister_error_unsupportedBinding_preserves_proofLayerInvariantBundle`, `adapterReadMemory_error_unsupportedBinding_preserves_proofLayerInvariantBundle` |

The error-case preservation theorems are trivially true (the state is unchanged on
error). The success-path theorems are substantive: they prove that adapter transitions
satisfying the `RuntimeBoundaryContract` and `AdapterProofHooks` obligations preserve
the composed invariant bundle over genuinely changed state.
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
    vspaceInvariantBundle st

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
  rcases hInv with ⟨hUniq, hNonOverlap, hConsist, hWx, hBound, hCrossAsid⟩
  exact ⟨by exact hUniq, by exact hNonOverlap, by exact hConsist, by exact hWx, by exact hBound, by exact hCrossAsid⟩

/-- WS-E3/H-07: Register writes preserve VSpace invariant bundle.
Register-only state changes do not affect the object store or ASID table. -/
private theorem writeRegisterState_preserves_vspaceInvariantBundle
    (reg : SeLe4n.RegName) (value : SeLe4n.RegValue) (st : SystemState)
    (hInv : vspaceInvariantBundle st) :
    vspaceInvariantBundle (writeRegisterState reg value st) := by
  rcases hInv with ⟨hUniq, hNonOverlap, hConsist, hWx, hBound, hCrossAsid⟩
  exact ⟨by exact hUniq, by exact hNonOverlap, by exact hConsist, by exact hWx, by exact hBound, by exact hCrossAsid⟩

-- ============================================================================
-- L-06/WS-E3: Default SystemState initialization proofs
-- ============================================================================

/-- L-06/WS-E3: The default (empty) `SystemState` satisfies the full composed
`proofLayerInvariantBundle`. This provides the base case for invariant induction:
the system starts in a valid state. All invariant components hold vacuously
because the empty state has no objects, no threads, no services, and an empty
scheduler. -/
private theorem default_schedulerInvariantBundle :
    schedulerInvariantBundle (default : SystemState) := by
  -- kernelInvariant = queueCurrentConsistent ∧ runQueueUnique ∧ currentThreadValid
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
  intro oid ntfn hObj; have h : (default : SystemState).objects[oid]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)

private theorem default_lifecycleInvariantBundle :
    lifecycleInvariantBundle (default : SystemState) :=
  lifecycleInvariantBundle_of_metadata_consistent _ default_systemState_lifecycleConsistent

private theorem default_ipcSchedulerContractPredicates :
    ipcSchedulerContractPredicates (default : SystemState) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tid tcb hObj; have h : (default : SystemState).objects[tid.toObjId]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)
  · intro tid tcb eid hObj; have h : (default : SystemState).objects[tid.toObjId]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)
  · intro tid tcb eid hObj; have h : (default : SystemState).objects[tid.toObjId]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)
  · intro tid tcb eid hObj; have h : (default : SystemState).objects[tid.toObjId]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)
  · intro tid tcb eid rt hObj; have h : (default : SystemState).objects[tid.toObjId]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)
  · intro tid tcb nid hObj; have h : (default : SystemState).objects[tid.toObjId]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)

/-- WS-H4 refactor: Extract default-state capabilityInvariantBundle construction
to eliminate 4x duplication in `default_system_state_proofLayerInvariantBundle`.
All components are vacuously true (empty objects/cdtNodeSlot) or use
`CapDerivationTree.empty_edgeWellFounded`. -/
private theorem default_capabilityInvariantBundle :
    capabilityInvariantBundle (default : SystemState) :=
  ⟨by intro oid cn hObj; have h : (default : SystemState).objects[oid]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp),
   by intro oid cn s c hObj; have h : (default : SystemState).objects[oid]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp),
   by intro oid cn hObj; have h : (default : SystemState).objects[oid]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp),
   by intro _ _ h; simp [default] at h,
   by exact CapDerivationTree.empty_edgeWellFounded,
   by intro cnodeId cn hObj; have h : (default : SystemState).objects[cnodeId]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)⟩

-- WS-H12e: Default-state proofs for new invariant components

private theorem default_dualQueueSystemInvariant :
    dualQueueSystemInvariant (default : SystemState) := by
  constructor
  · intro epId ep hObj; have h : (default : SystemState).objects[epId]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)
  · constructor
    · intro a tcbA hObj; have h : (default : SystemState).objects[a.toObjId]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)
    · intro b tcbB hObj; have h : (default : SystemState).objects[b.toObjId]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)

private theorem default_allPendingMessagesBounded :
    allPendingMessagesBounded (default : SystemState) := by
  intro tid tcb msg hObj; have h : (default : SystemState).objects[tid.toObjId]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)

private theorem default_badgeWellFormed :
    badgeWellFormed (default : SystemState) := by
  refine ⟨fun oid _ _ hObj => ?_, fun oid _ _ _ _ hObj => ?_⟩
  all_goals (have h : (default : SystemState).objects[oid]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp))

private theorem default_ipcInvariantFull :
    ipcInvariantFull (default : SystemState) :=
  ⟨default_ipcInvariant, default_dualQueueSystemInvariant, default_allPendingMessagesBounded,
   default_badgeWellFormed⟩

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
    have : (default : SystemState).scheduler.runnable = [] := by native_decide
    rw [this] at hMem; simp at hMem,
   by unfold currentTimeSlicePositive; simp,
   by unfold edfCurrentHasEarliestDeadline; simp,
   default_contextMatchesCurrent,
   default_runnableThreadsAreTCBs⟩

theorem default_system_state_proofLayerInvariantBundle :
    proofLayerInvariantBundle (default : SystemState) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  -- 6. serviceLifecycleCapabilityInvariantBundle = servicePolicySurface ∧ lifecycle ∧ capability
  · exact serviceLifecycleCapabilityInvariantBundle_of_components (default : SystemState)
      (by
        intro sid svc hSvc
        unfold lookupService at hSvc
        have hNone : (default : SystemState).services[sid]? = none := HashMap_getElem?_empty
        rw [hNone] at hSvc
        cases hSvc)
      default_lifecycleInvariantBundle
      default_capabilityInvariantBundle
  -- 7. vspaceInvariantBundle (6-conjunct: uniqueness ∧ non-overlap ∧ asidTableConsistent ∧ wxExclusive ∧ boundedAddr ∧ crossAsidIsolation)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro oid₁ oid₂ r₁ r₂ hObj₁; have h : (default : SystemState).objects[oid₁]? = none := HashMap_getElem?_empty; rw [h] at hObj₁; exact absurd hObj₁ (by simp)
    · intro oid root hObj; have h : (default : SystemState).objects[oid]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)
    · constructor
      · intro asid oid hLookup; have h : (default : SystemState).asidTable[asid]? = none := HashMap_getElem?_empty; rw [h] at hLookup; exact absurd hLookup (by simp)
      · intro oid root hObj; have h : (default : SystemState).objects[oid]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)
    · intro oid root v p perms hObj; have h : (default : SystemState).objects[oid]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)
    · intro oid root v p perms hObj; have h : (default : SystemState).objects[oid]? = none := HashMap_getElem?_empty; rw [h] at hObj; exact absurd hObj (by simp)
    · intro oidA oidB rA rB hObjA; have h : (default : SystemState).objects[oidA]? = none := HashMap_getElem?_empty; rw [h] at hObjA; exact absurd hObjA (by simp)

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
  obtain ⟨h1, h2, h3, h4⟩ := hIpc
  exact ⟨by exact h1, by exact h2, by exact h3, by exact h4⟩

theorem advanceTimerState_preserves_proofLayerInvariantBundle
    (ticks : Nat) (st : SystemState)
    (hInv : proofLayerInvariantBundle st) :
    proofLayerInvariantBundle (advanceTimerState ticks st) := by
  obtain ⟨hSched, hCap, hIpc, hCoupling, hLife, hSvc, hVsp⟩ := hInv
  refine ⟨by exact hSched,
         advanceTimerState_preserves_capabilityInvariantBundle ticks st hCap,
         ?_, ?_, by exact hLife, ?_, ?_⟩
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
  · obtain ⟨hP, hL, hC⟩ := hSvc
    exact ⟨by exact hP, by exact hL,
           advanceTimerState_preserves_capabilityInvariantBundle ticks st hC⟩
  -- vspaceInvariantBundle
  · exact advanceTimerState_preserves_vspaceInvariantBundle ticks st hVsp

end SeLe4n.Kernel.Architecture
