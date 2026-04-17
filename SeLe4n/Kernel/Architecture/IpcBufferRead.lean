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
- `ipcBufferReadMr : SystemState → ThreadId → Nat → Except IpcBufferReadError UInt64`
  is structurally read-only: the return type contains no `SystemState`, so
  Lean's type system guarantees no state modification. The function reads the
  TCB, the VSpace root, the mapping table, and the physical memory, but
  never writes.
- All failure modes surface as an abstract `IpcBufferReadError` that callers
  collapse into a single `KernelError.invalidMessageInfo` (matching seL4).
- The read scope is the caller's own IPC buffer only — every access is keyed
  on the `tid` argument, with no iteration over the object index or other
  threads' state. See `ipcBufferReadMr_reads_only_caller_tcb` for the
  formal witness of this property.

**Layout contract (matches `rust/sele4n-abi/src/ipc_buffer.rs`):**
- `tcb.ipcBuffer` is the VAddr of the start of the overflow region.
- Overflow slot `i` (0-indexed) occupies bytes `[i*8, i*8+8)` from that
  base — i.e., MR[i+4] for the ARM64 4-inline-regs layout.
- The first 64 overflow slots (= MR 4..67) are always within the same 4 KiB
  page as the buffer base, regardless of `ipcBufferAlignment` (512 B). Slots
  64..115 (MR 68..119) may straddle a page boundary; `root.lookup` is called
  per-slot, so any unmapped page in that range is correctly rejected.

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

    **Read-only:** structural — return type contains no `SystemState`, so
    Lean's type system forbids state modification. See
    `ipcBufferReadMr_reads_only_caller_tcb` for the NI witness. -/
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

/-- AK4-A.1: Out-of-range index — reads above `maxOverflowSlots` fail. -/
theorem ipcBufferReadMr_out_of_range
    (st : SystemState) (tid : ThreadId) (idx : Nat)
    (hGe : idx ≥ maxOverflowSlots) :
    ipcBufferReadMr st tid idx = .error .overflowIndexOutOfRange := by
  unfold ipcBufferReadMr
  split
  · rfl
  · omega

/-- AK4-A.1: Bounds — a successful read implies `idx < maxOverflowSlots`. -/
theorem ipcBufferReadMr_ok_bound
    (st : SystemState) (tid : ThreadId) (idx : Nat) (val : UInt64)
    (hOk : ipcBufferReadMr st tid idx = .ok val) :
    idx < maxOverflowSlots := by
  unfold ipcBufferReadMr at hOk
  split at hOk
  · simp at hOk
  · omega

/-- AK4-A.1: A successful read implies the caller TCB exists in the object
    store (substantive precondition — not a tautology). -/
theorem ipcBufferReadMr_ok_implies_tcb
    (st : SystemState) (tid : ThreadId) (idx : Nat) (val : UInt64)
    (hOk : ipcBufferReadMr st tid idx = .ok val) :
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) := by
  unfold ipcBufferReadMr at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · rename_i _ tcb hTcb
      exact ⟨tcb, hTcb⟩
    · simp at hOk

/-- AK4-A.5 (NI): The read scope is exclusively the caller's own state.
    Formally, replacing any other thread's state (its TCB, or any object
    that is neither the caller's TCB nor the caller's VSpaceRoot) does not
    change the read result. This is the substantive NI property of
    `ipcBufferReadMr` — the decode path has no cross-thread information
    channel. -/
theorem ipcBufferReadMr_reads_only_caller_tcb
    (st st' : SystemState) (tid : ThreadId) (idx : Nat)
    (hTcb  : st'.objects[tid.toObjId]? = st.objects[tid.toObjId]?)
    (hVs   : ∀ vs : SeLe4n.ObjId,
              (st.objects[tid.toObjId]?).bind
                 (fun o => match o with | .tcb t => some t.vspaceRoot | _ => none)
                 = some vs →
              st'.objects[vs]? = st.objects[vs]?)
    (hMem  : st'.machine.memory = st.machine.memory) :
    ipcBufferReadMr st' tid idx = ipcBufferReadMr st tid idx := by
  unfold ipcBufferReadMr
  by_cases hBound : idx ≥ maxOverflowSlots
  · simp [hBound]
  · simp only [hBound, ↓reduceIte]
    rw [hTcb]
    -- After rewriting the TCB lookup, case-split on the result.
    cases hT : st.objects[tid.toObjId]? with
    | none => rfl
    | some obj =>
      cases obj with
      | tcb tcb =>
        -- The VSpaceRoot lookup must also agree; supply witness via hVs.
        have hVsEq : st'.objects[tcb.vspaceRoot]? = st.objects[tcb.vspaceRoot]? := by
          apply hVs
          simp [hT]
        simp only [hVsEq, hMem]
      | endpoint _ => rfl
      | notification _ => rfl
      | cnode _ => rfl
      | vspaceRoot _ => rfl
      | untyped _ => rfl
      | schedContext _ => rfl

end SeLe4n.Kernel.Architecture.IpcBufferRead
