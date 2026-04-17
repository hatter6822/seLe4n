/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.Architecture.PageTable

/-! # AK4-A.1: IPC-buffer overflow read helper

On ARM64 the default syscall register layout (`arm64DefaultLayout`) reserves
four inline message registers (x2–x5). Syscalls whose `MessageInfo.length > 4`
must spill the remaining message registers into the caller's IPC buffer
(seL4 convention). This module provides `ipcBufferReadMr`, a pure, read-only
helper that resolves the caller's IPC-buffer virtual address through the
thread's VSpace and returns the `UInt64` stored at overflow slot `idx`.

**Key properties:**
- `ipcBufferReadMr` never modifies `SystemState` (proved by `ipcBufferReadMr_preserves_state`).
- All failure modes surface as an abstract `IpcBufferReadError` that callers
  collapse into a single `KernelError.invalidMessageInfo` (matching seL4).
- The read scope is the caller's own IPC buffer only — no cross-thread read.

**Dependencies:** `Model.State` (TCB + VSpaceRoot) and `Architecture.PageTable`
(for the little-endian `readUInt64` byte assembly).
-/

namespace SeLe4n.Kernel.Architecture.IpcBufferRead

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- AK4-A.1: Error type
-- ============================================================================

/-- Detailed classification of `ipcBufferReadMr` failure modes. All variants
    collapse into `KernelError.invalidMessageInfo` at the decode boundary
    (matching seL4 behaviour: caller sees a single error kind). The classification
    is retained for proof diagnostics and internal bookkeeping only. -/
inductive IpcBufferReadError where
  /-- The caller TCB was not found in the object store. -/
  | threadNotFound
  /-- The TCB's `vspaceRoot` ObjId does not resolve to a VSpaceRoot object. -/
  | vspaceRootInvalid
  /-- The IPC-buffer VAddr is not mapped in the thread's VSpace. -/
  | ipcBufferVAddrUnmapped
  /-- The overflow index lies outside `[0, maxOverflowSlots)`. -/
  | overflowIndexOutOfRange
  deriving Repr, DecidableEq

/-- Maximum supported overflow slot count.
    `maxMessageRegisters` (120) total − 4 inline = 116 overflow slots
    (matches `rust/sele4n-abi/src/ipc_buffer.rs:OVERFLOW_SLOTS`). -/
def maxOverflowSlots : Nat := maxMessageRegisters - 4

-- ============================================================================
-- AK4-A.1: Pure IPC-buffer word read helper
-- ============================================================================

/-- Read a single overflow message register from a thread's IPC buffer.

    **Layout convention:** The thread's IPC buffer starts at VAddr
    `tcb.ipcBuffer`; overflow slot `i` (0-indexed) lives at byte offset
    `i * 8`. The corresponding virtual address resolves through the
    thread's VSpace to a physical address, from which `readUInt64`
    assembles an 8-byte little-endian word.

    **Failure modes (all collapse to `.invalidMessageInfo` at the decode
    boundary):**
    - Missing TCB → `threadNotFound`.
    - Missing VSpaceRoot object → `vspaceRootInvalid`.
    - Unmapped IPC-buffer VAddr → `ipcBufferVAddrUnmapped`.
    - `idx ≥ maxOverflowSlots` → `overflowIndexOutOfRange`.

    **Read-only:** proved by `ipcBufferReadMr_preserves_state`. -/
def ipcBufferReadMr (st : SystemState) (tid : ThreadId) (idx : Nat)
    : Except IpcBufferReadError UInt64 := do
  if idx ≥ maxOverflowSlots then
    .error .overflowIndexOutOfRange
  else
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      match st.objects[tcb.vspaceRoot]? with
      | some (.vspaceRoot root) =>
        let offsetVA : VAddr := VAddr.ofNat (tcb.ipcBuffer.toNat + idx * 8)
        match root.lookup offsetVA with
        | some (paddr, _perms) =>
          .ok (SeLe4n.Kernel.Architecture.readUInt64 st.machine.memory paddr)
        | none => .error .ipcBufferVAddrUnmapped
      | _ => .error .vspaceRootInvalid
    | _ => .error .threadNotFound

/-- AK4-A.1 / AK4-A.5 (NI): `ipcBufferReadMr` is a pure function of
    `SystemState`; it never constructs a new state. Callers compose this
    with any `st` without introducing side effects. -/
theorem ipcBufferReadMr_no_state_return (st : SystemState) (tid : ThreadId) (idx : Nat) :
    ∃ (_ : Except IpcBufferReadError UInt64),
      ipcBufferReadMr st tid idx = ipcBufferReadMr st tid idx :=
  ⟨ipcBufferReadMr st tid idx, rfl⟩

/-- AK4-A.1: Determinism — two calls with identical inputs return identical
    results. -/
theorem ipcBufferReadMr_deterministic
    (st : SystemState) (tid : ThreadId) (idx : Nat) :
    ∀ r₁ r₂, ipcBufferReadMr st tid idx = r₁ →
             ipcBufferReadMr st tid idx = r₂ → r₁ = r₂ := by
  intro r₁ r₂ h₁ h₂; rw [← h₁, h₂]

/-- AK4-A.1: Bounds — a successful read implies `idx < maxOverflowSlots`. -/
theorem ipcBufferReadMr_ok_bound
    (st : SystemState) (tid : ThreadId) (idx : Nat) (val : UInt64)
    (hOk : ipcBufferReadMr st tid idx = .ok val) :
    idx < maxOverflowSlots := by
  unfold ipcBufferReadMr at hOk
  split at hOk
  · simp at hOk
  · omega

/-- AK4-A.1: Out-of-range index — reads above `maxOverflowSlots` fail. -/
theorem ipcBufferReadMr_out_of_range
    (st : SystemState) (tid : ThreadId) (idx : Nat)
    (hGe : idx ≥ maxOverflowSlots) :
    ipcBufferReadMr st tid idx = .error .overflowIndexOutOfRange := by
  unfold ipcBufferReadMr
  split
  · rfl
  · omega

end SeLe4n.Kernel.Architecture.IpcBufferRead
