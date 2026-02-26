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
but not included in the top-level composed bundle. -/
def proofLayerInvariantBundle (st : SystemState) : Prop :=
  schedulerInvariantBundle st ∧
    capabilityInvariantBundle st ∧
    m3IpcSeedInvariantBundle st ∧
    m35IpcSchedulerInvariantBundle st ∧
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
Timer-only state changes do not affect the object store. -/
private theorem advanceTimerState_preserves_vspaceInvariantBundle
    (ticks : Nat) (st : SystemState)
    (hInv : vspaceInvariantBundle st) :
    vspaceInvariantBundle (advanceTimerState ticks st) := by
  rcases hInv with ⟨hUniq, hNonOverlap⟩
  exact ⟨by exact hUniq, by exact hNonOverlap⟩

/-- WS-E3/H-07: Register writes preserve VSpace invariant bundle.
Register-only state changes do not affect the object store. -/
private theorem writeRegisterState_preserves_vspaceInvariantBundle
    (reg : SeLe4n.RegName) (value : SeLe4n.RegValue) (st : SystemState)
    (hInv : vspaceInvariantBundle st) :
    vspaceInvariantBundle (writeRegisterState reg value st) := by
  rcases hInv with ⟨hUniq, hNonOverlap⟩
  exact ⟨by exact hUniq, by exact hNonOverlap⟩

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
  constructor
  · intro oid ep hObj; simp at hObj
  · intro oid ntfn hObj; simp at hObj

private theorem default_lifecycleInvariantBundle :
    lifecycleInvariantBundle (default : SystemState) :=
  lifecycleInvariantBundle_of_metadata_consistent _ default_systemState_lifecycleConsistent

private theorem default_ipcSchedulerContractPredicates :
    ipcSchedulerContractPredicates (default : SystemState) := by
  refine ⟨?_, ?_, ?_⟩
  · intro tid tcb hObj; simp at hObj
  · intro tid tcb eid hObj; simp at hObj
  · intro tid tcb eid hObj; simp at hObj

theorem default_system_state_proofLayerInvariantBundle :
    proofLayerInvariantBundle (default : SystemState) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. schedulerInvariantBundle
  · exact default_schedulerInvariantBundle
  -- 2. capabilityInvariantBundle
  · exact ⟨by intro oid cn hObj; simp at hObj,
           by intro oid cn s c hObj; simp at hObj,
           by intro p c r b hMint; exact cspaceAttenuationRule_holds p c r b hMint,
           by exact lifecycleAuthorityMonotonicity_holds _⟩
  -- 3. m3IpcSeedInvariantBundle
  · exact ⟨default_schedulerInvariantBundle,
           ⟨by intro oid cn hObj; simp at hObj,
            by intro oid cn s c hObj; simp at hObj,
            by intro p c r b hMint; exact cspaceAttenuationRule_holds p c r b hMint,
            by exact lifecycleAuthorityMonotonicity_holds _⟩,
           default_ipcInvariant⟩
  -- 4. m35IpcSchedulerInvariantBundle
  · exact ⟨⟨default_schedulerInvariantBundle,
            ⟨by intro oid cn hObj; simp at hObj,
             by intro oid cn s c hObj; simp at hObj,
             by intro p c r b hMint; exact cspaceAttenuationRule_holds p c r b hMint,
             by exact lifecycleAuthorityMonotonicity_holds _⟩,
            default_ipcInvariant⟩,
           default_ipcSchedulerContractPredicates.1,
           default_ipcSchedulerContractPredicates.2⟩
  -- 5. lifecycleInvariantBundle
  · exact default_lifecycleInvariantBundle
  -- 6. serviceLifecycleCapabilityInvariantBundle = servicePolicySurface ∧ lifecycle ∧ capability
  · exact ⟨by intro sid svc hSvc; simp [lookupService] at hSvc,
           default_lifecycleInvariantBundle,
           by intro oid cn hObj; simp at hObj,
           by intro oid cn s c hObj; simp at hObj,
           by intro p c r b hMint; exact cspaceAttenuationRule_holds p c r b hMint,
           by exact lifecycleAuthorityMonotonicity_holds _⟩
  -- 7. vspaceInvariantBundle
  · constructor
    · intro oid₁ oid₂ r₁ r₂ hObj₁; simp at hObj₁
    · intro oid root hObj; simp at hObj

-- ============================================================================
-- M-08/WS-E6: Architecture assumption consumption theorems
-- ============================================================================

/-! ## M-08/WS-E6: Connecting assumptions to proofs

Architecture assumptions (enumerated in `Assumptions.lean`) are structural
declarations about platform behavior. This section provides **consumption
theorems** that demonstrate how each assumption is used in adapter
preservation proofs. The key insight: adapter transitions only succeed when
the `RuntimeBoundaryContract` predicates hold, and the `AdapterProofHooks`
structure requires proof that invariants are preserved under those predicates.

### Assumption-to-proof binding matrix

| Assumption | Contract predicate consumed | Adapter operation | Preservation theorem |
|---|---|---|---|
| `deterministicTimerProgress` | `timerMonotonic` | `adapterAdvanceTimer` | `adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle` |
| `deterministicRegisterContext` | `registerContextStable` | `adapterWriteRegister` | `adapterWriteRegister_ok_preserves_proofLayerInvariantBundle` |
| `memoryAccessSafety` | `memoryAccessAllowed` | `adapterReadMemory` | `adapterReadMemory_ok_preserves_proofLayerInvariantBundle` |
| `bootObjectTyping` | `objectTypeMetadataConsistent` | (boot-time, not runtime) | `default_system_state_proofLayerInvariantBundle` |
| `irqRoutingTotality` | `irqHandlerMapped` | (deferred to IRQ adapter) | Structural only |
-/

/-- M-08/WS-E6: Timer monotonicity assumption is consumed by the advance-timer
adapter path. When the contract admits the step, the assumption guarantees that
the timer value strictly increases, which is used by the `AdapterProofHooks`
to establish that the post-state satisfies the invariant bundle. -/
theorem deterministicTimerProgress_consumed_by_advanceTimer
    (contract : RuntimeBoundaryContract)
    (hooks : AdapterProofHooks contract)
    (ticks : Nat)
    (st : SystemState)
    (hTicks : ticks ≠ 0)
    (hMono : contract.timerMonotonic st (advanceTimerState ticks st))
    (hInv : proofLayerInvariantBundle st) :
    proofLayerInvariantBundle (advanceTimerState ticks st) :=
  hooks.preserveAdvanceTimer ticks st hInv hMono hTicks

/-- M-08/WS-E6: Register context stability assumption is consumed by the
write-register adapter path. -/
theorem deterministicRegisterContext_consumed_by_writeRegister
    (contract : RuntimeBoundaryContract)
    (hooks : AdapterProofHooks contract)
    (reg : SeLe4n.RegName)
    (value : SeLe4n.RegValue)
    (st : SystemState)
    (hStable : contract.registerContextStable st (writeRegisterState reg value st))
    (hInv : proofLayerInvariantBundle st) :
    proofLayerInvariantBundle (writeRegisterState reg value st) :=
  hooks.preserveWriteRegister reg value st hInv hStable

/-- M-08/WS-E6: Memory access safety assumption is consumed by the read-memory
adapter path. The read is pure (no state change), so preservation is immediate. -/
theorem memoryAccessSafety_consumed_by_readMemory
    (contract : RuntimeBoundaryContract)
    (hooks : AdapterProofHooks contract)
    (addr : SeLe4n.PAddr)
    (st : SystemState)
    (hAllow : contract.memoryAccessAllowed st addr)
    (hInv : proofLayerInvariantBundle st) :
    proofLayerInvariantBundle st :=
  hooks.preserveReadMemory addr st hInv hAllow

end SeLe4n.Kernel.Architecture
