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

/-- WS-H15d/A-42: The simulation restrictive proof hooks compose with the
adapter preservation theorems: any successful adapter operation under the
restrictive contract preserves `proofLayerInvariantBundle`. Since the
restrictive contract rejects all operations, no successful path exists —
the theorem is vacuously true but structurally witnesses the composition. -/
theorem simRestrictive_adapter_preserves_bundle
    (st st' : SystemState) (ticks : Nat)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterAdvanceTimer simRuntimeContractRestrictive ticks st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle
    simRuntimeContractRestrictive simRestrictiveAdapterProofHooks
    ticks st st' hInv hOk

end SeLe4n.Platform.Sim
