/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.Architecture.VSpace

/-! # D3: IPC Buffer Configuration

Implements `validateIpcBufferAddress` and `setIPCBufferOp` — the kernel
operation for `seL4_TCB_SetIPCBuffer`. The IPC buffer is a user-space
memory region used for message transfer; the kernel must validate that
the specified address is mapped, writable, properly aligned, and within
the thread's VSpace before accepting it.

**Key design decisions:**
- Validation looks up the VSpaceRoot directly from the TCB's `vspaceRoot`
  ObjId rather than going through the ASID table, since the TCB already
  carries the binding.
- The thread does NOT need to be suspended — seL4 allows changing the IPC
  buffer of a running thread (takes effect on next IPC operation).
- `ipcBuffer` is the only TCB field modified, making frame preservation
  trivial for all invariant bundles.
-/

namespace SeLe4n.Kernel.Architecture.IpcBufferValidation

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- D3-D: IPC buffer address validation
-- ============================================================================

/-- D3-D: Validate an IPC buffer address for a given thread.

Six-step validation pipeline:
1. Alignment: `addr.toNat % ipcBufferAlignment = 0`
2. Canonical address: `addr.toNat < VAddr.canonicalBound` (ARM64 48-bit VA)
3. Cross-page safety: guaranteed by step 1 — see `ipcBuffer_within_page`
4. VSpace root validity: thread's `vspaceRoot` resolves to a VSpaceRoot object
5. Mapping check: address is mapped in the thread's VSpace
6. Write permission: mapped page has `write = true`

AE4-H (U-32/A-IB01): Cross-page boundary safety is guaranteed by the
alignment check (step 1): since `ipcBufferAlignment = 512` divides the
ARM64 page size (4096), any 512-byte-aligned buffer of ≤512 bytes fits
entirely within a single 4KB page. See `ipcBuffer_within_page` below.

Returns `.error` with appropriate error code on any failure. -/
def validateIpcBufferAddress (st : SystemState) (tid : ThreadId)
    (addr : VAddr) : Except KernelError Unit :=
  -- Step 1: Alignment check
  if addr.toNat % ipcBufferAlignment != 0 then .error .alignmentError
  -- Step 2: Canonical address check
  else if !addr.isCanonical then .error .addressOutOfBounds
  else
    -- Look up the thread's TCB
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      -- Step 3: VSpace root validity
      match st.objects[tcb.vspaceRoot]? with
      | some (.vspaceRoot root) =>
        -- Step 4: Mapping check via VSpaceRoot.lookup
        match root.lookup addr with
        | some (_, perms) =>
          -- Step 5: Write permission check
          if perms.write then .ok ()
          else .error .translationFault
        | none => .error .translationFault
      | _ => .error .invalidArgument
    | _ => .error .objectNotFound

-- ============================================================================
-- D3-E: setIPCBufferOp — the complete operation
-- ============================================================================

/-- D3-E: Set a thread's IPC buffer address after validation.

Sequence:
1. Validate the address (alignment, canonical, mapped, writable)
2. Look up the target TCB
3. Update `tcb.ipcBuffer := addr`
4. Store the updated TCB

The thread does NOT need to be suspended — seL4 allows changing the IPC
buffer of a running thread (the change takes effect on next IPC operation). -/
def setIPCBufferOp (st : SystemState) (tid : ThreadId)
    (addr : VAddr) : Except KernelError SystemState :=
  match validateIpcBufferAddress st tid addr with
  | .error e => .error e
  | .ok () =>
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      -- AH3-B (L-08): Delegate to `storeObject` instead of manual struct-with.
      -- `storeObject` handles objects/objectIndex/objectIndexSet/lifecycle/asidTable
      -- uniformly. For TCB-to-TCB updates, asidTable is a no-op and capabilityRefs
      -- filter is a no-op (TCBs are never CNodes), producing identical state.
      let tcb' := { tcb with ipcBuffer := addr }
      match storeObject tid.toObjId (.tcb tcb') st with
      | .ok ((), st') => .ok st'
      | .error e => .error e
    | _ => .error .objectNotFound

-- ============================================================================
-- D3-G: Validation correctness theorems
-- ============================================================================

/-- D3-G: If validation succeeds, the address is aligned. -/
theorem validateIpcBufferAddress_implies_aligned
    (st : SystemState) (tid : ThreadId) (addr : VAddr)
    (hOk : validateIpcBufferAddress st tid addr = .ok ()) :
    addr.toNat % ipcBufferAlignment = 0 := by
  unfold validateIpcBufferAddress at hOk
  split at hOk
  · exact absurd hOk (by simp)
  · next h =>
    simp only [bne, Bool.not_eq_true, BEq.beq, Bool.not_eq_false'] at h
    exact of_decide_eq_true h

/-- D3-G: If validation succeeds, the address is canonical (within 48-bit VA space). -/
theorem validateIpcBufferAddress_implies_canonical
    (st : SystemState) (tid : ThreadId) (addr : VAddr)
    (hOk : validateIpcBufferAddress st tid addr = .ok ()) :
    addr.isCanonical = true := by
  unfold validateIpcBufferAddress at hOk
  split at hOk
  · contradiction
  · split at hOk
    · simp at hOk
    · simp_all

/-- D3-G: If validation succeeds, the address is mapped in the thread's VSpace
    with write permission. -/
theorem validateIpcBufferAddress_implies_mapped_writable
    (st : SystemState) (tid : ThreadId) (addr : VAddr)
    (hOk : validateIpcBufferAddress st tid addr = .ok ()) :
    ∃ tcb root paddr perms,
      st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      st.objects[tcb.vspaceRoot]? = some (.vspaceRoot root) ∧
      root.lookup addr = some (paddr, perms) ∧
      perms.write = true := by
  unfold validateIpcBufferAddress at hOk
  split at hOk
  · contradiction
  · split at hOk
    · contradiction
    · rename_i hAlign hCanon
      split at hOk
      · rename_i hTcb
        split at hOk
        · rename_i hVs
          split at hOk
          · rename_i hLookup
            split at hOk
            · exact ⟨_, _, _, _, hTcb, hVs, hLookup, by assumption⟩
            · contradiction
          · contradiction
        · contradiction
      · contradiction

/-- AE4-H (U-32/A-IB01): IPC buffer cross-page safety.

The IPC buffer (512 bytes) never crosses a page boundary when the address
is aligned to `ipcBufferAlignment` (512 bytes). Since 512 divides the ARM64
page size (4096 = 512 × 8), any 512-aligned offset within a page leaves at
least 512 bytes before the next page boundary.

This theorem guarantees that a single VSpace page-table lookup at `addr`
covers the entire IPC buffer region `[addr, addr + 512)`. -/
theorem ipcBuffer_within_page (addr : VAddr)
    (hAligned : addr.toNat % ipcBufferAlignment = 0) :
    addr.toNat / 4096 = (addr.toNat + ipcBufferAlignment - 1) / 4096 := by
  -- ipcBufferAlignment = 512. Since 512 | addr, addr % 4096 ∈ {0, 512, ..., 3584}.
  -- addr + 511 has the same page index because 3584 + 511 = 4095 < 4096.
  simp only [ipcBufferAlignment] at hAligned ⊢
  omega

-- ============================================================================
-- D3-F: Transport lemmas — setIPCBufferOp preserves non-object state fields
-- ============================================================================

/-- D3-F: Helper to extract the success branch of setIPCBufferOp. -/
private theorem setIPCBufferOp_success_shape
    (st st' : SystemState) (tid : ThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st tid addr = .ok st') :
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      validateIpcBufferAddress st tid addr = .ok () := by
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · rename_i hVal
    split at hOk
    · exact ⟨_, by assumption, hVal⟩
    · contradiction

/-- D3-F: `setIPCBufferOp` preserves the scheduler state.
    The operation only modifies `objects`, `objectIndex`, `objectIndexSet`,
    and `lifecycle`; all other SystemState fields are untouched. -/
theorem setIPCBufferOp_scheduler_eq
    (st st' : SystemState) (tid : ThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st tid addr = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · split at hOk
    · cases hOk; rfl
    · contradiction

/-- D3-F: `setIPCBufferOp` preserves the service registry. -/
theorem setIPCBufferOp_serviceRegistry_eq
    (st st' : SystemState) (tid : ThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st tid addr = .ok st') :
    st'.serviceRegistry = st.serviceRegistry := by
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · split at hOk
    · cases hOk; rfl
    · contradiction

/-- D3-F: `setIPCBufferOp` preserves IRQ handlers. -/
theorem setIPCBufferOp_irqHandlers_eq
    (st st' : SystemState) (tid : ThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st tid addr = .ok st') :
    st'.irqHandlers = st.irqHandlers := by
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · split at hOk
    · cases hOk; rfl
    · contradiction

/-- D3-F: `setIPCBufferOp` preserves machine state. -/
theorem setIPCBufferOp_machine_eq
    (st st' : SystemState) (tid : ThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st tid addr = .ok st') :
    st'.machine = st.machine := by
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · split at hOk
    · -- AH3-B: Unfold storeObject — machine is not in the `with` clause
      unfold storeObject at hOk; simp only [] at hOk; cases hOk; rfl
    · contradiction

/-- D3-F/AH3-B: `setIPCBufferOp` preserves the ASID table. After refactoring to
    `storeObject`, the ASID table is preserved because TCBs are not VSpaceRoots
    (both the clear and set branches of `storeObject.asidTable` are no-ops). -/
theorem setIPCBufferOp_asidTable_eq
    (st st' : SystemState) (tid : ThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st tid addr = .ok st') :
    st'.asidTable = st.asidTable := by
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · split at hOk
    · rename_i tcb hLookup
      unfold storeObject at hOk; simp only [] at hOk; cases hOk
      simp only [hLookup]
    · contradiction

/-- D3-F/AH3-B: `setIPCBufferOp` delegates to `storeObject`, which applies the
    standard capability-ref cleanup (filtering refs where the stored object's
    ObjId is the CNode). For TCB objects this is a no-op in well-formed states
    since TCBs are never CNodes — no `CapabilityRef` entries have `ref.cnode =
    tid.toObjId`. The filtered result is the canonical `storeObject` behavior. -/
theorem setIPCBufferOp_capabilityRefs_cleaned
    (st st' : SystemState) (tid : ThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st tid addr = .ok st') :
    st'.lifecycle.capabilityRefs =
      st.lifecycle.capabilityRefs.filter (fun ref _ => decide (ref.cnode ≠ tid.toObjId)) := by
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · split at hOk
    · rename_i tcb _
      unfold storeObject at hOk; simp only [] at hOk; cases hOk; rfl
    · contradiction

/-- D3-F: `setIPCBufferOp` determinism — the operation is a pure function
    of its inputs. -/
theorem setIPCBufferOp_deterministic
    (st : SystemState) (tid : ThreadId) (addr : VAddr) :
    ∀ st₁ st₂,
      setIPCBufferOp st tid addr = .ok st₁ →
      setIPCBufferOp st tid addr = .ok st₂ →
      st₁ = st₂ := by
  intro st₁ st₂ h₁ h₂
  rw [h₁] at h₂
  exact Except.ok.inj h₂

end SeLe4n.Kernel.Architecture.IpcBufferValidation
