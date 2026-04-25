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

Seven-step validation pipeline:
1. Alignment: `addr.toNat % ipcBufferAlignment = 0`
2. Canonical address: `addr.toNat < VAddr.canonicalBound` (ARM64 48-bit VA)
3. Cross-page safety: guaranteed by step 1 — see `ipcBuffer_within_page`
4. VSpace root validity: thread's `vspaceRoot` resolves to a VSpaceRoot object
5. Mapping check: address is mapped in the thread's VSpace
6. Write permission: mapped page has `write = true`
7. Physical address bounds: mapped PA within `2^physicalAddressWidth` (AJ4-C)

AE4-H (U-32/A-IB01): Cross-page boundary safety is guaranteed by the
alignment check (step 1): since `ipcBufferAlignment = 512` divides the
ARM64 page size (4096), any 512-byte-aligned buffer of ≤512 bytes fits
entirely within a single 4KB page. See `ipcBuffer_within_page` below.

AJ4-C (L-06): Step 7 checks the physical address returned by the VSpace
lookup against the platform's physical address width from `MachineState`.
Without this check, a mapped VA could theoretically reference a PA outside
the valid physical memory range (e.g., > 2^44 on RPi5 BCM2712).

Returns `.error` with appropriate error code on any failure. -/
def validateIpcBufferAddress (st : SystemState) (tid : ThreadId)
    (addr : VAddr) : Except KernelError Unit :=
  -- Step 1: Alignment check
  if addr.toNat % ipcBufferAlignment != 0 then .error .alignmentError
  -- Step 2: Canonical address check
  else if !addr.isCanonical then .error .addressOutOfBounds
  else
    -- Look up the thread's TCB.  AN10-B (DEF-AK7-F.reader.hygiene):
    -- typed-helper migration. Both pre-AN10 `_` arms collapsed
    -- wrong-variant and absent into the same error, so migration is
    -- semantics-preserving.
    match st.getTcb? tid with
    | some tcb =>
      -- Step 4: VSpace root validity
      match st.getVSpaceRoot? tcb.vspaceRoot with
      | some root =>
        -- Step 5: Mapping check via VSpaceRoot.lookup
        match root.lookup addr with
        | some (paddr, perms) =>
          -- Step 6: Write permission check
          if !perms.write then .error .translationFault
          -- Step 7: Physical address bounds check (AJ4-C / L-06)
          --
          -- AK3-F (A-M02 / MEDIUM): Check the END of the IPC buffer fits
          -- within the platform's physical address range, not just the start.
          -- An IPC buffer occupies `[paddr, paddr + ipcBufferAlignment)` (512
          -- bytes, by AE4-H / `ipcBuffer_within_page`). Without end-PA
          -- validation, a buffer starting at `2^width − 256` would pass the
          -- start-PA check but extend past the PA window into address
          -- space that's undefined on hardware.
          else if !(paddr.toNat + ipcBufferAlignment ≤
                    2^st.machine.physicalAddressWidth) then
            .error .addressOutOfBounds
          else .ok ()
        | none => .error .translationFault
      | none => .error .invalidArgument
    | none => .error .objectNotFound

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
buffer of a running thread (the change takes effect on next IPC operation).

**AL8 (WS-AL / AK7-E.cascade) — Type-level validity discipline**: the
`tid` parameter has type `ValidThreadId` to make sentinel-ID rejection
non-bypassable at compile time. Uses `vtid.val` directly (no `let`
binding) so `split at` tactics in preservation proofs can pattern-match
the `Except` branches without going through a let-layer. -/
def setIPCBufferOp (st : SystemState) (vtid : ValidThreadId)
    (addr : VAddr) : Except KernelError SystemState :=
  match validateIpcBufferAddress st vtid.val addr with
  | .error e => .error e
  | .ok () =>
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
    match st.getTcb? vtid.val with
    | some tcb =>
      -- AH3-B (L-08): Delegate to `storeObject` instead of manual struct-with.
      -- `storeObject` handles objects/objectIndex/objectIndexSet/lifecycle/asidTable
      -- uniformly. For TCB-to-TCB updates, asidTable is a no-op and capabilityRefs
      -- filter is a no-op (TCBs are never CNodes), producing identical state.
      let tcb' := { tcb with ipcBuffer := addr }
      match storeObject vtid.val.toObjId (.tcb tcb') st with
      | .ok ((), st') => .ok st'
      | .error e => .error e
    | none => .error .objectNotFound

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

/-- D3-G / AK3-F: If validation succeeds, the address is mapped in the
    thread's VSpace with write permission and the ENTIRE IPC buffer
    (`[paddr, paddr + ipcBufferAlignment)`) fits within the platform's
    physical address range.

    AK3-F (A-M02 / MEDIUM): Strengthened from `paddr.toNat < 2^width` to
    `paddr.toNat + ipcBufferAlignment ≤ 2^width` so every byte accessed by
    the kernel IPC subsystem is within valid PA space. -/
theorem validateIpcBufferAddress_implies_mapped_writable
    (st : SystemState) (tid : ThreadId) (addr : VAddr)
    (hOk : validateIpcBufferAddress st tid addr = .ok ()) :
    ∃ tcb root paddr perms,
      st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      st.objects[tcb.vspaceRoot]? = some (.vspaceRoot root) ∧
      root.lookup addr = some (paddr, perms) ∧
      perms.write = true ∧
      paddr.toNat + ipcBufferAlignment ≤ 2^st.machine.physicalAddressWidth := by
  unfold validateIpcBufferAddress at hOk
  split at hOk
  · contradiction
  · split at hOk
    · contradiction
    · rename_i hAlign hCanon
      split at hOk
      · rename_i tcb hTcb
        split at hOk
        · rename_i root hVs
          split at hOk
          · rename_i hLookup
            split at hOk
            · contradiction
            · rename_i hWrite
              split at hOk
              · contradiction
              · rename_i hPA
                simp only [Bool.not_eq_true, Bool.not_eq_false'] at hWrite hPA
                -- AN10-B: post-migration `validateIpcBufferAddress` reads
                -- via `getTcb?` and `getVSpaceRoot?`; bridge each typed-
                -- helper hypothesis to the raw lookup form expected by
                -- the post-condition.
                have hTcbRaw : st.objects[tid.toObjId]? = some (.tcb tcb) :=
                  (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
                have hVsRaw : st.objects[tcb.vspaceRoot]? = some (.vspaceRoot root) :=
                  (SystemState.getVSpaceRoot?_eq_some_iff st tcb.vspaceRoot root).mp hVs
                exact ⟨_, _, _, _, hTcbRaw, hVsRaw, hLookup,
                  by simp_all, by simp_all [decide_eq_true_eq]⟩
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
    (st st' : SystemState) (vtid : ValidThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st vtid addr = .ok st') :
    ∃ tcb, st.objects[vtid.val.toObjId]? = some (.tcb tcb) ∧
      validateIpcBufferAddress st vtid.val addr = .ok () := by
  -- AN10-B: post-migration `setIPCBufferOp` reads via `getTcb?`; bridge
  -- the typed-helper hypothesis to the raw lookup form expected by the
  -- post-condition.
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · rename_i hVal
    split at hOk
    · rename_i tcb hTcbTyped
      have hTcbRaw : st.objects[vtid.val.toObjId]? = some (.tcb tcb) :=
        (SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hTcbTyped
      exact ⟨tcb, hTcbRaw, hVal⟩
    · contradiction

/-- D3-F: `setIPCBufferOp` preserves the scheduler state.
    The operation only modifies `objects`, `objectIndex`, `objectIndexSet`,
    and `lifecycle`; all other SystemState fields are untouched. -/
theorem setIPCBufferOp_scheduler_eq
    (st st' : SystemState) (vtid : ValidThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st vtid addr = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · split at hOk
    · cases hOk; rfl
    · contradiction

/-- D3-F: `setIPCBufferOp` preserves the service registry. -/
theorem setIPCBufferOp_serviceRegistry_eq
    (st st' : SystemState) (vtid : ValidThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st vtid addr = .ok st') :
    st'.serviceRegistry = st.serviceRegistry := by
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · split at hOk
    · cases hOk; rfl
    · contradiction

/-- D3-F: `setIPCBufferOp` preserves IRQ handlers. -/
theorem setIPCBufferOp_irqHandlers_eq
    (st st' : SystemState) (vtid : ValidThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st vtid addr = .ok st') :
    st'.irqHandlers = st.irqHandlers := by
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · split at hOk
    · cases hOk; rfl
    · contradiction

/-- D3-F: `setIPCBufferOp` preserves machine state. -/
theorem setIPCBufferOp_machine_eq
    (st st' : SystemState) (vtid : ValidThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st vtid addr = .ok st') :
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
    (st st' : SystemState) (vtid : ValidThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st vtid addr = .ok st') :
    st'.asidTable = st.asidTable := by
  -- AN10-B: post-migration `setIPCBufferOp` reads via `getTcb?`; bridge
  -- to the raw lookup form expected by `storeObject`'s asidTable
  -- match-on-objects branch.
  unfold setIPCBufferOp at hOk
  split at hOk
  · contradiction
  · split at hOk
    · rename_i tcb hLookup
      have hRaw : st.objects[vtid.val.toObjId]? = some (.tcb tcb) :=
        (SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hLookup
      unfold storeObject at hOk; simp only [] at hOk; cases hOk
      simp only [hRaw]
    · contradiction

/-- D3-F/AH3-B: `setIPCBufferOp` delegates to `storeObject`, which applies the
    standard capability-ref cleanup (filtering refs where the stored object's
    ObjId is the CNode). For TCB objects this is a no-op in well-formed states
    since TCBs are never CNodes — no `CapabilityRef` entries have `ref.cnode =
    tid.toObjId`. The filtered result is the canonical `storeObject` behavior. -/
theorem setIPCBufferOp_capabilityRefs_cleaned
    (st st' : SystemState) (vtid : ValidThreadId) (addr : VAddr)
    (hOk : setIPCBufferOp st vtid addr = .ok st') :
    st'.lifecycle.capabilityRefs =
      st.lifecycle.capabilityRefs.filter (fun ref _ => decide (ref.cnode ≠ vtid.val.toObjId)) := by
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
    (st : SystemState) (vtid : ValidThreadId) (addr : VAddr) :
    ∀ st₁ st₂,
      setIPCBufferOp st vtid addr = .ok st₁ →
      setIPCBufferOp st vtid addr = .ok st₂ →
      st₁ = st₂ := by
  intro st₁ st₂ h₁ h₂
  rw [h₁] at h₂
  exact Except.ok.inj h₂

end SeLe4n.Kernel.Architecture.IpcBufferValidation
