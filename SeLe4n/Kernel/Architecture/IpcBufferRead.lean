-- SPDX-License-Identifier: GPL-3.0-or-later
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

/-- The virtual address of overflow slot `idx` in a thread's IPC buffer.

    The single source for this arithmetic: the read below resolves it, and
    the SM7.F access-time TLB fill caches the page it resolves through.  Two
    copies could drift apart, and a fill that cached a different page than the
    read walked would be a fill of an entry hardware never loaded. -/
def ipcBufferSlotAddr (ipcBuffer : VAddr) (idx : Nat) : VAddr :=
  VAddr.ofNat (ipcBuffer.toNat + idx * 8)

/-- The page through which overflow slot `idx` resolves.

    The single source shared by `ipcBufferReadMr` below (which looks the page
    up) and the SM7.F access-time TLB fill (which caches it): the fill must
    cache *the page the read walked*, and stating that arithmetic twice is how
    the two would drift.  Being a page base is what makes an entry keyed here
    reachable by a page invalidation — `tlbEntryMatches` compares virtual
    addresses for equality, not containment, so an entry keyed at an unaligned
    byte address would survive the shootdown that is supposed to evict it. -/
def ipcBufferSlotPage (ipcBuffer : VAddr) (idx : Nat) : VAddr :=
  (ipcBufferSlotAddr ipcBuffer idx).pageBase

/-- The page a slot resolves through is page-aligned. -/
theorem ipcBufferSlotPage_aligned (ipcBuffer : VAddr) (idx : Nat) :
    (ipcBufferSlotPage ipcBuffer idx).toNat % pageBytes = 0 :=
  VAddr.pageBase_aligned _

/-- Read a single overflow message register from a thread's IPC buffer.

    **Layout convention:** The thread's IPC buffer starts at VAddr
    `tcb.ipcBuffer`; overflow slot `i` (0-indexed) lives at byte offset
    `i * 8`. The corresponding virtual address resolves through the
    thread's VSpace to a physical address, from which `readUInt64`
    assembles an 8-byte little-endian word.

    **Translation is page-granular.** `VSpaceRoot.mappings` is an exact-key
    table whose keys are page bases (`VSpaceRoot.mapPage` installs no other
    key), so the slot's *byte* address must be split: the containing page is
    looked up, and the intra-page offset is carried through to the physical
    address.  Handing the raw byte address to `lookup` — as this function did
    before v0.32.150 — misses for every slot but the zeroth, so a syscall
    carrying two or more overflow registers failed with
    `ipcBufferVAddrUnmapped` against a correctly mapped buffer, and slot zero
    resolved only because its offset happens to be zero.  seL4 routinely
    carries many message registers through the IPC buffer; the truncation was
    a model-fidelity defect, fail-closed but real.

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
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration on
    -- both the TCB and VSpaceRoot lookups. Both `_` arms in the
    -- pre-AN10 form collapsed wrong-variant and absent into the same
    -- error code, so migration is semantics-preserving.
    match st.getTcb? tid with
    | some tcb =>
      match st.getVSpaceRoot? tcb.vspaceRoot with
      | some root =>
        let slotVA : VAddr := ipcBufferSlotAddr tcb.ipcBuffer idx
        -- Page-granular translation: resolve the containing page, then carry
        -- the intra-page offset through to the physical address.
        match root.lookup (ipcBufferSlotPage tcb.ipcBuffer idx) with
        | some (paddr, _perms) =>
          .ok (SeLe4n.Kernel.Architecture.readUInt64 st.machine.memory
                 (PAddr.ofNat (paddr.toNat + slotVA.pageOffset)))
        | none => .error .ipcBufferVAddrUnmapped
      | none => .error .vspaceRootInvalid
    | none => .error .threadNotFound

/-- **WS-SM SM7.F.5**: the positive characterisation — what a *successful*
    read resolves to.  The failure-mode theorems below say when the read
    fails; this one pins the physical address it reads from when it succeeds,
    which is what the access-time TLB fill must agree with.

    Note the shape: the page comes from `ipcBufferSlotPage` and the offset
    from `ipcBufferSlotAddr`, so the address read is
    `page's physical base + the slot's offset within the page`. -/
theorem ipcBufferReadMr_ok_of_mapped
    (st : SystemState) (tid : ThreadId) (tcb : SeLe4n.Model.TCB)
    (root : SeLe4n.Model.VSpaceRoot) (idx : Nat)
    (pa : SeLe4n.PAddr) (perms : SeLe4n.Model.PagePermissions)
    (hBound : idx < maxOverflowSlots)
    (hTcb : st.getTcb? tid = some tcb)
    (hRoot : st.getVSpaceRoot? tcb.vspaceRoot = some root)
    (hMapped : root.lookup (ipcBufferSlotPage tcb.ipcBuffer idx)
                 = some (pa, perms)) :
    ipcBufferReadMr st tid idx
      = .ok (SeLe4n.Kernel.Architecture.readUInt64 st.machine.memory
               (PAddr.ofNat
                 (pa.toNat + (ipcBufferSlotAddr tcb.ipcBuffer idx).pageOffset))) := by
  unfold ipcBufferReadMr
  split
  · next hGe => exact absurd hGe (by omega)
  · simp only [hTcb, hRoot, hMapped]

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
  -- AN10-B: post-migration `ipcBufferReadMr` reads via `getTcb?`; bridge
  -- via the iff lemma so the existing post-condition (raw lookup) holds.
  unfold ipcBufferReadMr at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · rename_i _ tcb hTcb
      exact ⟨tcb, (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb⟩
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
  -- AN10-B: unfold both `getTcb?` and `getVSpaceRoot?` so the framing
  -- hypotheses (stated against the raw object-store lookup) line up
  -- with what `ipcBufferReadMr` now reads via the typed helpers.
  unfold ipcBufferReadMr SystemState.getTcb? SystemState.getVSpaceRoot?
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
      | reply _ => rfl

end SeLe4n.Kernel.Architecture.IpcBufferRead
