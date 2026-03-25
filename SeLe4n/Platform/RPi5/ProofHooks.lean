import SeLe4n.Kernel.Architecture.Invariant
import SeLe4n.Platform.RPi5.RuntimeContract

/-!
# Raspberry Pi 5 — Concrete AdapterProofHooks

WS-H15d/A-33: Concrete `AdapterProofHooks` instantiation for the RPi5
platform's restrictive runtime contract.

The restrictive contract (`rpi5RuntimeContractRestrictive`) shares the
production contract's timer monotonicity and RAM-only memory access
predicates but denies all register writes (`registerContextStable := False`).

## Timer preservation

Timer advancement only modifies `machine.timer`, leaving all invariant-relevant
fields unchanged. The proof delegates to the generic
`advanceTimerState_preserves_proofLayerInvariantBundle` lemma, which handles
the decomposition of all 7 invariant-bundle components.

## Register write preservation

The restrictive contract rejects all register writes, making the proof
obligation vacuously satisfiable: the contract hypothesis is `False`, from
which any conclusion follows via `absurd`.

## Memory read preservation

Read operations are state-preserving — the pre-state is returned unchanged.
The proof is `fun _ st hInv _ => hInv`.

## Design note: production contract (U6-C/D strengthened)

The production `rpi5RuntimeContract` was strengthened in U6-C to require
that when a thread is scheduled, the machine register file matches the
TCB's `registerContext` field. This replaces the previous permissive
disjunct (`sp preserved ∨ context switch in progress`).

The restrictive contract still denies all register writes
(`registerContextStable := False`), so proof hooks remain vacuously correct
for the write path. A future context-switch-aware adapter (WS-V) will
combine register-file load with `scheduler.current` update atomically,
enabling proof hooks for the production contract.
-/

namespace SeLe4n.Platform.RPi5

open SeLe4n.Kernel.Architecture
open SeLe4n.Model

/-- WS-H15d/A-33: Concrete `AdapterProofHooks` for the RPi5 restrictive
runtime contract. Timer preservation uses the generic lemma;
register write is vacuous; memory read is state-preserving. -/
def rpi5RestrictiveAdapterProofHooks :
    AdapterProofHooks rpi5RuntimeContractRestrictive where
  preserveAdvanceTimer := fun ticks st hInv _ _ =>
    advanceTimerState_preserves_proofLayerInvariantBundle ticks st hInv
  preserveWriteRegister := fun _ _ _ _ hStable =>
    absurd hStable (by simp [rpi5RuntimeContractRestrictive])
  preserveReadMemory := fun _ st hInv _ => hInv

/-- WS-H15d/A-33: End-to-end timer advancement preservation for RPi5.
Composes the restrictive proof hooks with the generic adapter preservation
theorem. Since the restrictive contract rejects register writes, only
timer and memory-read paths can succeed; the theorem is substantive for
timer advancement. -/
theorem rpi5Restrictive_adapterAdvanceTimer_preserves
    (st st' : SystemState) (ticks : Nat)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterAdvanceTimer rpi5RuntimeContractRestrictive ticks st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle
    rpi5RuntimeContractRestrictive rpi5RestrictiveAdapterProofHooks
    ticks st st' hInv hOk

/-- WS-H15d/A-33: End-to-end register write preservation for RPi5 (vacuous).
The restrictive contract rejects all register writes; the theorem is
vacuously true because no successful write path exists. -/
theorem rpi5Restrictive_adapterWriteRegister_preserves
    (st st' : SystemState) (reg : SeLe4n.RegName) (value : SeLe4n.RegValue)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterWriteRegister rpi5RuntimeContractRestrictive reg value st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterWriteRegister_ok_preserves_proofLayerInvariantBundle
    rpi5RuntimeContractRestrictive rpi5RestrictiveAdapterProofHooks
    reg value st st' hInv hOk

/-- WS-H15d/A-33: End-to-end memory read preservation for RPi5.
Read operations are state-preserving — the pre-state invariant carries
through directly. -/
theorem rpi5Restrictive_adapterReadMemory_preserves
    (st st' : SystemState) (addr : SeLe4n.PAddr) (byte : UInt8)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterReadMemory rpi5RuntimeContractRestrictive addr st = .ok (byte, st')) :
    proofLayerInvariantBundle st' :=
  adapterReadMemory_ok_preserves_proofLayerInvariantBundle
    rpi5RuntimeContractRestrictive rpi5RestrictiveAdapterProofHooks
    addr st st' byte hInv hOk

end SeLe4n.Platform.RPi5
