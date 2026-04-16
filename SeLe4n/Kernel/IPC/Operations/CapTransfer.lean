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
- Non-fatal failures (`.noSlot`, `.grantDenied`) do NOT abort remaining transfers.
- The sender retains all transferred capabilities (IPC transfer is copy).

**Key operation**: `ipcUnwrapCaps` — iterates over `msg.caps`, threading state
and advancing the receiver's slot base only after successful insertion.  On
error (missing CNode root or insert failure), the slot base is NOT advanced
and the loop short-circuits: all remaining caps are filled with `.noSlot` via
`fillRemainingNoSlot`.  This avoids slot gaps in the receiver's CNode and
aligns with seL4's cursor-preservation semantics, while the short-circuit
exploits the observation that error conditions persist (the receiver's CSpace
root hasn't changed, so subsequent transfers would fail identically).

**Error-to-noSlot conversion (F-03/AD2-C):** When `ipcTransferSingleCap` fails
(e.g., receiver CSpace root not found, or slot insertion error), the error is
converted to `.noSlot` in the transfer results array by `ipcUnwrapCapsLoop`.
Remaining capabilities in the batch are padded with `.noSlot` via short-circuit
semantics. This matches seL4's cursor-preservation behavior: the receiver sees
a consistent result count regardless of individual transfer failures. The
conversion is intentional and does NOT mask security-relevant failures — the
receiver simply sees fewer successfully transferred capabilities, which is the
correct degraded behavior. No capability can be silently installed or lost;
the sender retains all originals.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Pad remaining cap transfer results with `.noSlot` for caps at indices
`idx, idx+1, ...` up to the fuel bound. Used to short-circuit when a fatal
error (e.g., receiver CSpace root not a CNode) makes all remaining transfers
impossible. Mirrors the array-bounds structure of `ipcUnwrapCapsLoop` so that
the result count matches exactly. -/
private def fillRemainingNoSlot
    (caps : Array Capability) (idx : Nat)
    (acc : Array CapTransferResult) (fuel : Nat) : Array CapTransferResult :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    match caps[idx]? with
    | none => acc
    | some _ => fillRemainingNoSlot caps (idx + 1) (acc.push .noSlot) fuel'

/-- M-D01: Recursive helper for unwrapping caps. Processes caps from index
`idx` to the end of the array. Termination is structural on `fuel`
(initially `caps.size - idx`).

**AK1-G (I-M05) — Internal recursion helper.** This function is the
recursive worker for `ipcUnwrapCaps` and **must only be called from
`ipcUnwrapCaps`** (which always supplies `idx := 0` and `accResults := #[]`).
Calling it externally with `idx > 0` produces off-by-one padding and
silently drops capabilities because the `fuel` parameter is keyed off
`caps.size - idx`. Making this `private` would fail the module build
because `IPC/DualQueue/WithCaps.lean` and
`Capability/Invariant/Preservation.lean` reference the associated
preservation theorems (`ipcUnwrapCapsLoop_preserves_*`) by name.

The static invariant `ipcUnwrapCaps` only calls this with `idx = 0` can be
verified by `grep -rn "ipcUnwrapCapsLoop " SeLe4n/Kernel/IPC/` — the only
production call site in code (non-proof) is at the `ipcUnwrapCaps`
recursion entry below. -/
def ipcUnwrapCapsLoop
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
            -- Fatal error: receiver CSpace root is not a CNode (or insert
            -- failed on a slot that findFirstEmptySlot said was empty, which
            -- is unreachable in the single-threaded model).  The error
            -- condition persists because state is unmodified, so all
            -- remaining caps would also fail.  Short-circuit: pad the
            -- results with `.noSlot` for every remaining cap and return
            -- immediately with the original state.  This avoids slot gaps
            -- in the receiver's CNode (no `nextBase` advancement on error)
            -- and aligns with seL4's cursor-preservation semantics.
            let finalResults :=
              fillRemainingNoSlot caps (idx + 1) (accResults.push .noSlot) fuel'
            .ok ({ results := finalResults }, st)
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
- Fatal errors (receiver CSpace root not a CNode) short-circuit the loop:
  remaining caps are filled with `.noSlot` and state is returned unchanged.
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

theorem ipcUnwrapCapsLoop_preserves_scheduler
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
        obtain ⟨_, rfl⟩ := hStep; rfl
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

theorem ipcUnwrapCapsLoop_preserves_services
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
        obtain ⟨_, rfl⟩ := hStep; rfl
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

theorem ipcUnwrapCapsLoop_preserves_objects_ne
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ receiverRoot)
    (hObjInv : st.objects.invExt)
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
        obtain ⟨_, rfl⟩ := hStep; rfl
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hObjInvNext := ipcTransferSingleCap_preserves_objects_invExt cap _ receiverRoot nextBase
          maxExtraCaps st stNext result hObjInv hTransfer
        have hObj := ipcTransferSingleCap_preserves_objects_ne cap _ receiverRoot nextBase
          maxExtraCaps st stNext result oid hNe hObjInv hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => rw [ih _ _ _ _ hObjInvNext hStep, hObj]
        | noSlot => rw [ih _ _ _ _ hObjInvNext hStep, hObj]
        | grantDenied => rw [ih _ _ _ _ hObjInvNext hStep, hObj]

/-- ipcUnwrapCaps preserves objects at keys other than the receiver root CNode. -/
theorem ipcUnwrapCaps_preserves_objects_ne
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ receiverRoot)
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
  · exact ipcUnwrapCapsLoop_preserves_objects_ne _ _ _ _ _ _ _ _ _ _ _ hNe hObjInv hStep

theorem ipcUnwrapCapsLoop_preserves_ntfn_objects
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st.objects[oid]? = some (.notification ntfn))
    (hObjInv : st.objects.invExt)
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
        obtain ⟨_, rfl⟩ := hStep; exact hNtfn
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hObjInvNext := ipcTransferSingleCap_preserves_objects_invExt cap _ receiverRoot nextBase
          maxExtraCaps st stNext result hObjInv hTransfer
        have hNtfnNext := ipcTransferSingleCap_preserves_ntfn_objects cap _ receiverRoot nextBase
          maxExtraCaps st stNext result oid ntfn hNtfn hObjInv hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hNtfnNext hObjInvNext hStep
        | noSlot => exact ih _ _ _ _ hNtfnNext hObjInvNext hStep
        | grantDenied => exact ih _ _ _ _ hNtfnNext hObjInvNext hStep

/-- M3-E4: ipcUnwrapCaps preserves all notification objects. Any notification
in st survives unchanged in st' because ipcUnwrapCaps only modifies CNode
objects (via cspaceInsertSlot at receiverRoot) and CDT fields. -/
theorem ipcUnwrapCaps_preserves_ntfn_objects
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st.objects[oid]? = some (.notification ntfn))
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    st'.objects[oid]? = some (.notification ntfn) := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hNtfn
  · exact ipcUnwrapCapsLoop_preserves_ntfn_objects _ _ _ _ _ _ _ _ _ _ _ _ hNtfn hObjInv hStep

theorem ipcUnwrapCapsLoop_receiverRoot_not_ntfn
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (hNotNtfn : ∀ ntfn, st.objects[receiverRoot]? ≠ some (.notification ntfn))
    (hObjInv : st.objects.invExt)
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
        obtain ⟨_, rfl⟩ := hStep; exact hNotNtfn
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hObjInvNext := ipcTransferSingleCap_preserves_objects_invExt cap _ receiverRoot nextBase
          maxExtraCaps st stNext result hObjInv hTransfer
        have hNextNotNtfn := ipcTransferSingleCap_receiverRoot_not_ntfn cap _
          receiverRoot nextBase maxExtraCaps st stNext result hObjInv hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hNextNotNtfn hObjInvNext hStep
        | noSlot => exact ih _ _ _ _ hNextNotNtfn hObjInvNext hStep
        | grantDenied => exact ih _ _ _ _ hNextNotNtfn hObjInvNext hStep

theorem ipcUnwrapCapsLoop_preserves_ep_objects
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects[oid]? = some (.endpoint ep))
    (hObjInv : st.objects.invExt)
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
        obtain ⟨_, rfl⟩ := hStep; exact hEp
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hObjInvNext := ipcTransferSingleCap_preserves_objects_invExt cap _ receiverRoot nextBase
          maxExtraCaps st stNext result hObjInv hTransfer
        have hEpNext := ipcTransferSingleCap_preserves_ep_objects cap _ receiverRoot nextBase
          maxExtraCaps st stNext result oid ep hEp hObjInv hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hEpNext hObjInvNext hStep
        | noSlot => exact ih _ _ _ _ hEpNext hObjInvNext hStep
        | grantDenied => exact ih _ _ _ _ hEpNext hObjInvNext hStep

/-- ipcUnwrapCaps preserves all endpoint objects. -/
theorem ipcUnwrapCaps_preserves_ep_objects
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects[oid]? = some (.endpoint ep))
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    st'.objects[oid]? = some (.endpoint ep) := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hEp
  · exact ipcUnwrapCapsLoop_preserves_ep_objects _ _ _ _ _ _ _ _ _ _ _ _ hEp hObjInv hStep

theorem ipcUnwrapCapsLoop_preserves_tcb_objects
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hTcb : st.objects[oid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
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
        obtain ⟨_, rfl⟩ := hStep; exact hTcb
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hObjInvNext := ipcTransferSingleCap_preserves_objects_invExt cap _ receiverRoot nextBase
          maxExtraCaps st stNext result hObjInv hTransfer
        have hTcbNext := ipcTransferSingleCap_preserves_tcb_objects cap _ receiverRoot nextBase
          maxExtraCaps st stNext result oid tcb hTcb hObjInv hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hTcbNext hObjInvNext hStep
        | noSlot => exact ih _ _ _ _ hTcbNext hObjInvNext hStep
        | grantDenied => exact ih _ _ _ _ hTcbNext hObjInvNext hStep

/-- ipcUnwrapCaps preserves all TCB objects. -/
theorem ipcUnwrapCaps_preserves_tcb_objects
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hTcb : st.objects[oid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    st'.objects[oid]? = some (.tcb tcb) := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hTcb
  · exact ipcUnwrapCapsLoop_preserves_tcb_objects _ _ _ _ _ _ _ _ _ _ _ _ hTcb hObjInv hStep

/-- M3-E4: ipcUnwrapCapsLoop preserves CNode type at receiverRoot.
If receiverRoot is a CNode before the loop, it remains a CNode after
(though the CNode contents may change as caps are inserted). -/
theorem ipcUnwrapCapsLoop_preserves_cnode_at_root
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (cn : CNode)
    (hCn : st.objects[receiverRoot]? = some (.cnode cn))
    (hObjInv : st.objects.invExt)
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
        obtain ⟨_, rfl⟩ := hStep; exact ⟨cn, hCn⟩
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        simp [hTransfer] at hStep
        have hObjInvNext := ipcTransferSingleCap_preserves_objects_invExt cap _ receiverRoot nextBase
          maxExtraCaps st stNext result hObjInv hTransfer
        have ⟨cn', hCn'⟩ := ipcTransferSingleCap_receiverRoot_stays_cnode cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st stNext result cn hCn hObjInv hTransfer
        cases result with
        | installed c s => exact ih _ _ _ _ _ hCn' hObjInvNext hStep
        | noSlot => exact ih _ _ _ _ _ hCn' hObjInvNext hStep
        | grantDenied => exact ih _ _ _ _ _ hCn' hObjInvNext hStep

/-- M3-E4: ipcUnwrapCaps preserves CNode type at receiverRoot. -/
theorem ipcUnwrapCaps_preserves_cnode_at_root
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (cn : CNode)
    (hCn : st.objects[receiverRoot]? = some (.cnode cn))
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    ∃ cn', st'.objects[receiverRoot]? = some (.cnode cn') := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact ⟨cn, hCn⟩
  · exact ipcUnwrapCapsLoop_preserves_cnode_at_root _ _ _ _ _ _ _ _ _ _ _ hCn hObjInv hStep

/-- M3-E4: receiverRoot is never a notification after ipcUnwrapCaps. In the
grant-denied path state is unchanged. In the loop, each ipcTransferSingleCap
either errors (state unchanged) or stores a CNode at receiverRoot. -/
theorem ipcUnwrapCaps_receiverRoot_not_ntfn
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hNotNtfn : ∀ ntfn, st.objects[receiverRoot]? ≠ some (.notification ntfn))
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    ∀ ntfn, st'.objects[receiverRoot]? ≠ some (.notification ntfn) := by
  unfold ipcUnwrapCaps at hStep
  split at hStep
  · simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hNotNtfn
  · exact ipcUnwrapCapsLoop_receiverRoot_not_ntfn _ _ _ _ _ _ _ _ _ _ hNotNtfn hObjInv hStep

end SeLe4n.Kernel
