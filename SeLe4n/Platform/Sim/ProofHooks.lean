-- SPDX-License-Identifier: GPL-3.0-or-later
import SeLe4n.Kernel.Architecture.Invariant
import SeLe4n.Platform.Sim.RuntimeContract

/-!
# Simulation Platform — Concrete AdapterProofHooks

WS-H15d/A-42: Concrete `AdapterProofHooks` instantiation for the simulation
platform's restrictive runtime contract.

The restrictive contract (`simRuntimeContractRestrictive`) sets all boundary
predicates to `False`, meaning the adapter rejects every timer advancement,
register write, and memory read. The `AdapterProofHooks` obligations are
therefore trivially satisfiable: the contract hypotheses are `False`, from
which any conclusion follows.

## Design note: permissive contract limitations

The permissive contract (`simRuntimeContractPermissive`) cannot instantiate
`AdapterProofHooks.preserveWriteRegister` because it admits all register
writes (`registerContextStable := True`), but `contextMatchesCurrent` (part
of `schedulerInvariantBundleFull`) equates `machine.regs` with the current
thread's `tcb.registerContext`. An unrestricted register write can break this
invariant. For testing purposes, the permissive contract is used with the
trace harness where formal invariant preservation is not required.
-/

namespace SeLe4n.Platform.Sim

open SeLe4n.Kernel.Architecture
open SeLe4n.Model

/-- WS-H15d/A-42: Concrete `AdapterProofHooks` for the simulation restrictive
runtime contract. All three proof obligations hold vacuously because the
restrictive contract rejects every operation (all predicates are `False`). -/
def simRestrictiveAdapterProofHooks :
    AdapterProofHooks simRuntimeContractRestrictive where
  preserveAdvanceTimer := fun _ _ _ hMono _ =>
    absurd hMono (by simp [simRuntimeContractRestrictive])
  preserveWriteRegister := fun _ _ _ _ hStable =>
    absurd hStable (by simp [simRuntimeContractRestrictive])
  preserveReadMemory := fun _ st hInv _ => hInv
  preserveContextSwitch := fun _ _ _ _ hStable =>
    absurd hStable (by simp [simRuntimeContractRestrictive])

/-- WS-H15d/A-33: End-to-end timer advancement preservation for Sim.
The restrictive contract rejects all timer operations, so the theorem is
vacuously true — no successful path exists. Structurally witnesses the
composition of proof hooks with the generic adapter preservation theorem. -/
theorem simRestrictive_adapterAdvanceTimer_preserves
    (st st' : SystemState) (ticks : Nat)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterAdvanceTimer simRuntimeContractRestrictive ticks st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle
    simRuntimeContractRestrictive simRestrictiveAdapterProofHooks
    ticks st st' hInv hOk

/-- WS-H15d/A-33: End-to-end register write preservation for Sim (vacuous).
The restrictive contract rejects all register writes. -/
theorem simRestrictive_adapterWriteRegister_preserves
    (st st' : SystemState) (reg : SeLe4n.RegName) (value : SeLe4n.RegValue)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterWriteRegister simRuntimeContractRestrictive reg value st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterWriteRegister_ok_preserves_proofLayerInvariantBundle
    simRuntimeContractRestrictive simRestrictiveAdapterProofHooks
    reg value st st' hInv hOk

/-- WS-H15d/A-33: End-to-end memory read preservation for Sim (vacuous).
The restrictive contract rejects all memory reads. -/
theorem simRestrictive_adapterReadMemory_preserves
    (st st' : SystemState) (addr : SeLe4n.PAddr) (byte : UInt8)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterReadMemory simRuntimeContractRestrictive addr st = .ok (byte, st')) :
    proofLayerInvariantBundle st' :=
  adapterReadMemory_ok_preserves_proofLayerInvariantBundle
    simRuntimeContractRestrictive simRestrictiveAdapterProofHooks
    addr st st' byte hInv hOk

-- ============================================================================
-- S5-D: Substantive AdapterProofHooks for simRuntimeContractSubstantive
-- ============================================================================

/-- S5-D: Concrete `AdapterProofHooks` for the simulation substantive runtime
contract. Timer preservation uses the generic lemma (substantive, not vacuous);
register write is vacuously satisfied (denied by contract); memory read is
state-preserving. -/
def simSubstantiveAdapterProofHooks :
    AdapterProofHooks simRuntimeContractSubstantive where
  preserveAdvanceTimer := fun ticks st hInv _ _ =>
    advanceTimerState_preserves_proofLayerInvariantBundle ticks st hInv
  preserveWriteRegister := fun _ _ _ _ hStable =>
    absurd hStable (by simp [simRuntimeContractSubstantive])
  preserveReadMemory := fun _ st hInv _ => hInv
  preserveContextSwitch := fun _ _ _ _ hStable =>
    absurd hStable (by simp [simRuntimeContractSubstantive])

/-- S5-D: End-to-end timer advancement preservation for Sim (substantive).
The substantive contract accepts timer operations when timer is monotonically
non-decreasing — the proof is non-vacuous and delegates to the generic
adapter preservation theorem. -/
theorem simSubstantive_adapterAdvanceTimer_preserves
    (st st' : SystemState) (ticks : Nat)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterAdvanceTimer simRuntimeContractSubstantive ticks st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle
    simRuntimeContractSubstantive simSubstantiveAdapterProofHooks
    ticks st st' hInv hOk

/-- S5-D: End-to-end register write preservation for Sim substantive (vacuous).
The substantive contract rejects all register writes. -/
theorem simSubstantive_adapterWriteRegister_preserves
    (st st' : SystemState) (reg : SeLe4n.RegName) (value : SeLe4n.RegValue)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterWriteRegister simRuntimeContractSubstantive reg value st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterWriteRegister_ok_preserves_proofLayerInvariantBundle
    simRuntimeContractSubstantive simSubstantiveAdapterProofHooks
    reg value st st' hInv hOk

/-- S5-D: End-to-end memory read preservation for Sim substantive.
Memory reads are state-preserving — the pre-state is returned unchanged. -/
theorem simSubstantive_adapterReadMemory_preserves
    (st st' : SystemState) (addr : SeLe4n.PAddr) (byte : UInt8)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterReadMemory simRuntimeContractSubstantive addr st = .ok (byte, st')) :
    proofLayerInvariantBundle st' :=
  adapterReadMemory_ok_preserves_proofLayerInvariantBundle
    simRuntimeContractSubstantive simSubstantiveAdapterProofHooks
    addr st st' byte hInv hOk

end SeLe4n.Platform.Sim
