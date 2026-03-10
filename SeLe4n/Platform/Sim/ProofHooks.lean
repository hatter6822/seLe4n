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

end SeLe4n.Platform.Sim
