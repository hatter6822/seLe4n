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

private theorem ipcUnwrapCapsLoop_preserves_services
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase accResults fuel st
             = .ok (summary, st')) :
    st'.services = st.services := by
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
        have hSvc := ipcTransferSingleCap_preserves_services cap _ receiverRoot nextBase
          maxExtraCaps st stNext result hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => rw [ih _ _ _ _ hStep, hSvc]
        | noSlot => rw [ih _ _ _ _ hStep, hSvc]
        | grantDenied => rw [ih _ _ _ _ hStep, hSvc]

theorem ipcUnwrapCaps_preserves_services
    (msg : IpcMessage)
    (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    st'.services = st.services := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
  · exact ipcUnwrapCapsLoop_preserves_services _ _ _ _ _ _ _ _ _ _ hStep

private theorem ipcUnwrapCapsLoop_preserves_objects_ne
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ receiverRoot)
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase accResults fuel st
             = .ok (summary, st')) :
    st'.objects[oid]? = st.objects[oid]? := by
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
        have hObj := ipcTransferSingleCap_preserves_objects_ne cap _ receiverRoot nextBase
          maxExtraCaps st stNext result oid hNe hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => rw [ih _ _ _ _ hStep, hObj]
        | noSlot => rw [ih _ _ _ _ hStep, hObj]
        | grantDenied => rw [ih _ _ _ _ hStep, hObj]

/-- ipcUnwrapCaps preserves objects at keys other than the receiver root CNode. -/
theorem ipcUnwrapCaps_preserves_objects_ne
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ receiverRoot)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
  · exact ipcUnwrapCapsLoop_preserves_objects_ne _ _ _ _ _ _ _ _ _ _ _ hNe hStep

private theorem ipcUnwrapCapsLoop_preserves_ntfn_objects
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st.objects[oid]? = some (.notification ntfn))
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase accResults fuel st
             = .ok (summary, st')) :
    st'.objects[oid]? = some (.notification ntfn) := by
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep; exact hNtfn
  | succ n ih =>
    simp only [ipcUnwrapCapsLoop] at hStep
    cases hCap : caps[idx]? with
    | none => simp [hCap] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hNtfn
    | some cap =>
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st with
      | error e =>
        simp [hTransfer] at hStep
        exact ih _ _ _ _ hNtfn hStep
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hNtfnNext := ipcTransferSingleCap_preserves_ntfn_objects cap _ receiverRoot nextBase
          maxExtraCaps st stNext result oid ntfn hNtfn hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hNtfnNext hStep
        | noSlot => exact ih _ _ _ _ hNtfnNext hStep
        | grantDenied => exact ih _ _ _ _ hNtfnNext hStep

/-- M3-E4: ipcUnwrapCaps preserves all notification objects. Any notification
in st survives unchanged in st' because ipcUnwrapCaps only modifies CNode
objects (via cspaceInsertSlot at receiverRoot) and CDT fields. -/
theorem ipcUnwrapCaps_preserves_ntfn_objects
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st.objects[oid]? = some (.notification ntfn))
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    st'.objects[oid]? = some (.notification ntfn) := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hNtfn
  · exact ipcUnwrapCapsLoop_preserves_ntfn_objects _ _ _ _ _ _ _ _ _ _ _ _ hNtfn hStep

private theorem ipcUnwrapCapsLoop_receiverRoot_not_ntfn
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (hNotNtfn : ∀ ntfn, st.objects[receiverRoot]? ≠ some (.notification ntfn))
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase accResults fuel st
             = .ok (summary, st')) :
    ∀ ntfn, st'.objects[receiverRoot]? ≠ some (.notification ntfn) := by
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep; exact hNotNtfn
  | succ n ih =>
    simp only [ipcUnwrapCapsLoop] at hStep
    cases hCap : caps[idx]? with
    | none => simp [hCap] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hNotNtfn
    | some cap =>
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st with
      | error e =>
        simp [hTransfer] at hStep
        exact ih _ _ _ _ hNotNtfn hStep
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hNextNotNtfn := ipcTransferSingleCap_receiverRoot_not_ntfn cap _
          receiverRoot nextBase maxExtraCaps st stNext result hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hNextNotNtfn hStep
        | noSlot => exact ih _ _ _ _ hNextNotNtfn hStep
        | grantDenied => exact ih _ _ _ _ hNextNotNtfn hStep

private theorem ipcUnwrapCapsLoop_preserves_ep_objects
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects[oid]? = some (.endpoint ep))
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase accResults fuel st
             = .ok (summary, st')) :
    st'.objects[oid]? = some (.endpoint ep) := by
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep; exact hEp
  | succ n ih =>
    simp only [ipcUnwrapCapsLoop] at hStep
    cases hCap : caps[idx]? with
    | none => simp [hCap] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hEp
    | some cap =>
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st with
      | error e =>
        simp [hTransfer] at hStep
        exact ih _ _ _ _ hEp hStep
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hEpNext := ipcTransferSingleCap_preserves_ep_objects cap _ receiverRoot nextBase
          maxExtraCaps st stNext result oid ep hEp hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hEpNext hStep
        | noSlot => exact ih _ _ _ _ hEpNext hStep
        | grantDenied => exact ih _ _ _ _ hEpNext hStep

/-- ipcUnwrapCaps preserves all endpoint objects. -/
theorem ipcUnwrapCaps_preserves_ep_objects
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects[oid]? = some (.endpoint ep))
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    st'.objects[oid]? = some (.endpoint ep) := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hEp
  · exact ipcUnwrapCapsLoop_preserves_ep_objects _ _ _ _ _ _ _ _ _ _ _ _ hEp hStep

private theorem ipcUnwrapCapsLoop_preserves_tcb_objects
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hTcb : st.objects[oid]? = some (.tcb tcb))
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase accResults fuel st
             = .ok (summary, st')) :
    st'.objects[oid]? = some (.tcb tcb) := by
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep; exact hTcb
  | succ n ih =>
    simp only [ipcUnwrapCapsLoop] at hStep
    cases hCap : caps[idx]? with
    | none => simp [hCap] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hTcb
    | some cap =>
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st with
      | error e =>
        simp [hTransfer] at hStep
        exact ih _ _ _ _ hTcb hStep
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hTcbNext := ipcTransferSingleCap_preserves_tcb_objects cap _ receiverRoot nextBase
          maxExtraCaps st stNext result oid tcb hTcb hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hTcbNext hStep
        | noSlot => exact ih _ _ _ _ hTcbNext hStep
        | grantDenied => exact ih _ _ _ _ hTcbNext hStep

/-- ipcUnwrapCaps preserves all TCB objects. -/
theorem ipcUnwrapCaps_preserves_tcb_objects
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hTcb : st.objects[oid]? = some (.tcb tcb))
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    st'.objects[oid]? = some (.tcb tcb) := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hTcb
  · exact ipcUnwrapCapsLoop_preserves_tcb_objects _ _ _ _ _ _ _ _ _ _ _ _ hTcb hStep

/-- M3-E4: ipcUnwrapCapsLoop preserves CNode type at receiverRoot.
If receiverRoot is a CNode before the loop, it remains a CNode after
(though the CNode contents may change as caps are inserted). -/
private theorem ipcUnwrapCapsLoop_preserves_cnode_at_root
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (cn : CNode)
    (hCn : st.objects[receiverRoot]? = some (.cnode cn))
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase accResults fuel st
             = .ok (summary, st')) :
    ∃ cn', st'.objects[receiverRoot]? = some (.cnode cn') := by
  induction fuel generalizing idx nextBase accResults st cn with
  | zero =>
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep; exact ⟨cn, hCn⟩
  | succ n ih =>
    simp only [ipcUnwrapCapsLoop] at hStep
    cases hCap : caps[idx]? with
    | none => simp [hCap] at hStep; obtain ⟨_, rfl⟩ := hStep; exact ⟨cn, hCn⟩
    | some cap =>
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st with
      | error e =>
        simp [hTransfer] at hStep
        exact ih _ _ _ _ _ hCn hStep
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        simp [hTransfer] at hStep
        have ⟨cn', hCn'⟩ := ipcTransferSingleCap_receiverRoot_stays_cnode cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st stNext result cn hCn hTransfer
        cases result with
        | installed c s => exact ih _ _ _ _ _ hCn' hStep
        | noSlot => exact ih _ _ _ _ _ hCn' hStep
        | grantDenied => exact ih _ _ _ _ _ hCn' hStep

/-- M3-E4: ipcUnwrapCaps preserves CNode type at receiverRoot. -/
theorem ipcUnwrapCaps_preserves_cnode_at_root
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (cn : CNode)
    (hCn : st.objects[receiverRoot]? = some (.cnode cn))
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    ∃ cn', st'.objects[receiverRoot]? = some (.cnode cn') := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact ⟨cn, hCn⟩
  · exact ipcUnwrapCapsLoop_preserves_cnode_at_root _ _ _ _ _ _ _ _ _ _ _ hCn hStep

/-- M3-E4: receiverRoot is never a notification after ipcUnwrapCaps. In the
grant-denied path state is unchanged. In the loop, each ipcTransferSingleCap
either errors (state unchanged) or stores a CNode at receiverRoot. -/
theorem ipcUnwrapCaps_receiverRoot_not_ntfn
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hNotNtfn : ∀ ntfn, st.objects[receiverRoot]? ≠ some (.notification ntfn))
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    ∀ ntfn, st'.objects[receiverRoot]? ≠ some (.notification ntfn) := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hNotNtfn
  · exact ipcUnwrapCapsLoop_receiverRoot_not_ntfn _ _ _ _ _ _ _ _ _ _ hNotNtfn hStep

end SeLe4n.Kernel
