/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Operations

/-! # IPC Capability Transfer Operations (M-D01 / WS-M3)

This module implements the batch capability unwrap operation for IPC rendezvous.
During an IPC send or call, the sender's `IpcMessage.caps` array carries extra
capabilities that should be installed into the receiver's CSpace when the
rendezvous completes.

**seL4 semantics**:
- The endpoint capability must have `Grant` right for any cap transfer to occur.
- If `Grant` is absent, all caps are silently dropped (`.grantDenied`).
- Each cap is independently transferred via `ipcTransferSingleCap`.
- Failures on individual caps do NOT abort remaining transfers.
- The sender retains all transferred capabilities (IPC transfer is copy).

**Key operation**: `ipcUnwrapCaps` — iterates over `msg.caps`, threading state
and advancing the receiver's slot base after each successful insertion.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- M-D01: Recursive helper for unwrapping caps. Processes caps from index
`idx` to the end of the array. Termination is structural on `fuel`
(initially `caps.size - idx`). -/
private def ipcUnwrapCapsLoop
    (caps : Array Capability)
    (senderCspaceRoot : SeLe4n.ObjId)
    (receiverCspaceRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot)
    (accResults : Array CapTransferResult)
    (fuel : Nat) : Kernel CapTransferSummary :=
  match fuel with
  | 0 => fun st => .ok ({ results := accResults }, st)
  | fuel' + 1 =>
    match caps[idx]? with
    | none => fun st => .ok ({ results := accResults }, st)
    | some cap =>
      fun st =>
        match ipcTransferSingleCap cap
            { cnode := senderCspaceRoot, slot := SeLe4n.Slot.ofNat 0 }
            receiverCspaceRoot nextBase maxExtraCaps st with
        | .error _e =>
            ipcUnwrapCapsLoop caps senderCspaceRoot receiverCspaceRoot
              (idx + 1) (SeLe4n.Slot.ofNat (nextBase.toNat + 1))
              (accResults.push .noSlot) fuel' st
        | .ok (result, stNext) =>
            let nextBase' := match result with
              | .installed _ _ => SeLe4n.Slot.ofNat (nextBase.toNat + 1)
              | _ => nextBase
            ipcUnwrapCapsLoop caps senderCspaceRoot receiverCspaceRoot
              (idx + 1) nextBase'
              (accResults.push result) fuel' stNext

/-- M-D01: Unwrap all extra capabilities from an IPC message into the
receiver's CSpace. This is the top-level cap-transfer entry point, called
during IPC rendezvous after message delivery.

seL4 semantics:
- If the endpoint capability lacks `Grant` right, all caps are skipped
  (returns array of `.grantDenied` results).
- Otherwise, each cap in `msg.caps` is transferred via
  `ipcTransferSingleCap`, scanning consecutive slots starting from
  `receiverSlotBase`. The scan window advances by 1 after each successful
  insertion to avoid overwriting.
- Failures on individual caps (`.noSlot`) do NOT abort the remaining
  transfers — each cap is independently processed.
- The sender retains all transferred capabilities (IPC transfer is copy). -/
def ipcUnwrapCaps
    (msg : IpcMessage)
    (senderCspaceRoot : SeLe4n.ObjId)
    (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot)
    (endpointGrantRight : Bool) : Kernel CapTransferSummary :=
  fun st =>
    if !endpointGrantRight then
      let results := msg.caps.map fun _ => CapTransferResult.grantDenied
      .ok ({ results }, st)
    else
      ipcUnwrapCapsLoop msg.caps senderCspaceRoot receiverCspaceRoot
        0 receiverSlotBase #[] msg.caps.size st

private theorem ipcUnwrapCapsLoop_preserves_scheduler
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase accResults fuel st
             = .ok (summary, st')) :
    st'.scheduler = st.scheduler := by
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep; rfl
  | succ n ih =>
    simp only [ipcUnwrapCapsLoop] at hStep
    cases hCap : caps[idx]? with
    | none => simp [hCap] at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
    | some cap =>
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st with
      | error e =>
        simp [hTransfer] at hStep
        exact ih _ _ _ _ hStep
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hSched := ipcTransferSingleCap_preserves_scheduler cap _ receiverRoot nextBase
          maxExtraCaps st stNext result hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => rw [ih _ _ _ _ hStep, hSched]
        | noSlot => rw [ih _ _ _ _ hStep, hSched]
        | grantDenied => rw [ih _ _ _ _ hStep, hSched]

theorem ipcUnwrapCaps_preserves_scheduler
    (msg : IpcMessage)
    (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    st'.scheduler = st.scheduler := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
  · exact ipcUnwrapCapsLoop_preserves_scheduler _ _ _ _ _ _ _ _ _ _ hStep

end SeLe4n.Kernel
