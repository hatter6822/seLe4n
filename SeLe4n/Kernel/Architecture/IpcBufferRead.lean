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
import SeLe4n.Kernel.Architecture.LittleEndianWords

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

/-- WS-ZA ZA5.2: the address of an entry's `i`-th word pair
(`MachineState.entryWordBytes`). -/
@[inline] def pairAddr (b : ByteArray) (i : Nat) : Nat := (le64At b (16 * i)).toNat

/-- WS-ZA ZA5.2: the word of an entry's `i`-th word pair. -/
@[inline] def pairWord (b : ByteArray) (i : Nat) : UInt64 := le64At b (16 * i + 8)

/-- The word at `pa` among the pairs `i, i + 1, …` (`k` of them), the first
match winning, else the model's `memory`. -/
def syncedWordFrom (mem : Memory) (b : ByteArray) (pa : PAddr) : Nat → Nat → UInt64
  | _, 0 => SeLe4n.Kernel.Architecture.readUInt64 mem pa
  | i, k + 1 =>
    if pairAddr b i = pa.toNat then pairWord b i else syncedWordFrom mem b pa (i + 1) k

/-- **WS-ZA ZA5.2: a word of a thread's IPC buffer at physical address `pa`, as
the syscall decode reads it** — the word this entry read from RAM there (the
first of the entry's `n` pairs naming `pa`), else the model's `memory`.  A
recursion over the pairs' bytes, so no `Option`, list or closure is built. -/
@[inline] def syncedWordAt (mem : Memory) (b : ByteArray) (n : Nat) (pa : PAddr) : UInt64 :=
  syncedWordFrom mem b pa 0 n

/-- `syncedWordAt` over a machine state: its entry's words ahead of its memory. -/
@[inline] def userWordAt (ms : MachineState) (pa : PAddr) : UInt64 :=
  syncedWordAt ms.memory ms.entryWordBytes ms.entryWordCount pa

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
          .ok (userWordAt st.machine (PAddr.ofNat (paddr.toNat + slotVA.pageOffset)))
        | none => .error .ipcBufferVAddrUnmapped
      | none => .error .vspaceRootInvalid
    | none => .error .threadNotFound

/-- WS-ZA ZA5.2: `ipcBufferReadMr` handing its word to a continuation
(`ipcBufferReadMrK_eq`).  Inlined into a caller, the word reaches the caller's
arm as a machine word: no `Except` cell boxes it. -/
@[inline] def ipcBufferReadMrK {α : Type} (st : SystemState) (tid : ThreadId) (idx : Nat)
    (err : IpcBufferReadError → α) (ok : UInt64 → α) : α :=
  if idx ≥ maxOverflowSlots then err .overflowIndexOutOfRange
  else
    match st.getTcb? tid with
    | some tcb =>
      match st.getVSpaceRoot? tcb.vspaceRoot with
      | some root =>
        match root.lookup (ipcBufferSlotPage tcb.ipcBuffer idx) with
        | some (paddr, _perms) =>
          ok (userWordAt st.machine
            (PAddr.ofNat (paddr.toNat + (ipcBufferSlotAddr tcb.ipcBuffer idx).pageOffset)))
        | none => err .ipcBufferVAddrUnmapped
      | none => err .vspaceRootInvalid
    | none => err .threadNotFound

theorem ipcBufferReadMrK_eq {α : Type} (st : SystemState) (tid : ThreadId) (idx : Nat)
    (err : IpcBufferReadError → α) (ok : UInt64 → α) :
    ipcBufferReadMrK st tid idx err ok =
      match ipcBufferReadMr st tid idx with
      | .ok w => ok w
      | .error e => err e := by
  unfold ipcBufferReadMrK ipcBufferReadMr
  by_cases hIdx : idx ≥ maxOverflowSlots
  · simp only [hIdx, ↓reduceIte]
  · simp only [hIdx, ↓reduceIte]
    cases st.getTcb? tid with
    | none => rfl
    | some tcb =>
      dsimp only
      cases st.getVSpaceRoot? tcb.vspaceRoot with
      | none => rfl
      | some root =>
        dsimp only
        cases root.lookup (ipcBufferSlotPage tcb.ipcBuffer idx) with
        | none => rfl
        | some p => rfl

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
      = .ok (userWordAt st.machine
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
    (hMem  : st'.machine.memory = st.machine.memory)
    (hBytes : st'.machine.entryWordBytes = st.machine.entryWordBytes)
    (hCount : st'.machine.entryWordCount = st.machine.entryWordCount) :
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
        simp only [hVsEq, userWordAt, hMem, hBytes, hCount]
      | endpoint _ => rfl
      | notification _ => rfl
      | cnode _ => rfl
      | vspaceRoot _ => rfl
      | untyped _ => rfl
      | schedContext _ => rfl
      | reply _ | frame _ | pageTable _ => rfl

-- ============================================================================
-- WS-BP BP7.8: the slot resolver both directions share, and the RAM sync
-- ============================================================================

/-- **WS-BP BP7.8: where overflow slot `idx` of a thread's IPC buffer lives in
RAM, as the kernel may touch it for that thread** — `none` unless the slot's
page resolves through the thread's own VSpace, the word is eight-byte aligned
(so it lies in one page), and the address is declared RAM (`addrInRange`, never
a device region).  `needWrite` additionally requires a writable mapping: a
delivered message register is written only where the receiver may write, which
is the permission check `ipcBufferReadMr` does not make and a write path must
(`AuditRead`'s stated non-goal, discharged).

It is the **one** resolver the two directions share: the entry reads a sender's
words from RAM at the addresses it answers (`callerOverflowAddrs`), and a
delivery writes a receiver's at the addresses it answers
(`Architecture.overflowDeliveryWrites`), so the kernel can name no address in
either direction that this function did not.  Since the HAL admits exactly an
eight-byte aligned word of RAM past the kernel's reserved extent
(`user_translation::user_word_admissible`), every address it answers is one the
HAL performs: a mapped frame is carved from an untyped, and the boot refuses an
untyped over the kernel's extent. -/
@[inline] def ipcBufferSlotPAddr? (st : SystemState) (tcb : SeLe4n.Model.TCB) (idx : Nat)
    (needWrite : Bool) : Option PAddr :=
  if idx < maxOverflowSlots then
    match st.getVSpaceRoot? tcb.vspaceRoot with
    | some root =>
      match root.lookup (ipcBufferSlotPage tcb.ipcBuffer idx) with
      | some (paddr, perms) =>
        let pa := PAddr.ofNat (paddr.toNat + (ipcBufferSlotAddr tcb.ipcBuffer idx).pageOffset)
        if pa.toNat % 8 == 0 && st.machine.addrInRange pa && (!needWrite || perms.write) then
          some pa
        else none
      | none => none
    | none => none
  else none

/-- **WS-BP BP7.8**: where the resolver answers, the read reads exactly that
word — so the entry's RAM sync and the decode's read name one address. -/
theorem ipcBufferReadMr_of_slotPAddr? (st : SystemState) (tid : ThreadId)
    (tcb : SeLe4n.Model.TCB) (idx : Nat) (needWrite : Bool) (pa : PAddr)
    (hTcb : st.getTcb? tid = some tcb)
    (hPa : ipcBufferSlotPAddr? st tcb idx needWrite = some pa) :
    ipcBufferReadMr st tid idx = .ok (userWordAt st.machine pa) := by
  unfold ipcBufferSlotPAddr? at hPa
  split at hPa
  · rename_i hBound
    split at hPa
    · rename_i root hRoot
      split at hPa
      · rename_i paddr perms hMapped
        dsimp only at hPa
        split at hPa
        · cases hPa
          exact ipcBufferReadMr_ok_of_mapped st tid tcb root idx paddr perms hBound hTcb
            hRoot hMapped
        · cases hPa
      · cases hPa
    · cases hPa
  · cases hPa

/-- An answered slot is eight-byte aligned. -/
theorem ipcBufferSlotPAddr?_aligned (st : SystemState) (tcb : SeLe4n.Model.TCB)
    (idx : Nat) (needWrite : Bool) (pa : PAddr)
    (hPa : ipcBufferSlotPAddr? st tcb idx needWrite = some pa) : pa.toNat % 8 = 0 := by
  unfold ipcBufferSlotPAddr? at hPa
  split at hPa
  · split at hPa
    · split at hPa
      · dsimp only at hPa
        split at hPa
        · rename_i hOk
          cases hPa
          simp only [Bool.and_eq_true, beq_iff_eq] at hOk
          exact hOk.1.1
        · cases hPa
      · cases hPa
    · cases hPa
  · cases hPa

/-- An answered slot is declared RAM. -/
theorem ipcBufferSlotPAddr?_ram (st : SystemState) (tcb : SeLe4n.Model.TCB)
    (idx : Nat) (needWrite : Bool) (pa : PAddr)
    (hPa : ipcBufferSlotPAddr? st tcb idx needWrite = some pa) :
    st.machine.addrInRange pa = true := by
  unfold ipcBufferSlotPAddr? at hPa
  split at hPa
  · split at hPa
    · split at hPa
      · dsimp only at hPa
        split at hPa
        · rename_i hOk
          cases hPa
          simp only [Bool.and_eq_true] at hOk
          exact hOk.1.2
        · cases hPa
      · cases hPa
    · cases hPa
  · cases hPa

/-- **How many overflow slots a `MessageInfo` word asks the decode to read**:
the message registers past the four inline ones, capped at the buffer's slots;
none for a word that does not decode. -/
def overflowStop (msgInfo : UInt64) : Nat :=
  match SeLe4n.Model.MessageInfo.decode msgInfo.toNat with
  | some mi => min (mi.length - 4) maxOverflowSlots
  | none => 0

/-- The compiled `overflowStop`: the fields read off the word itself, so a word
`≥ 2^63` builds no heap number. -/
@[inline] def overflowStopImpl (w : UInt64) : Nat :=
  let length := (w &&& 0x7F).toNat
  if length ≤ maxMessageRegisters && ((w >>> 7) &&& 0x3).toNat ≤ SeLe4n.Model.maxExtraCaps &&
      (w >>> 9).toNat ≤ SeLe4n.Model.MessageInfo.maxLabel then
    min (length - 4) maxOverflowSlots
  else 0

@[csimp] theorem overflowStop_eq_impl : @overflowStop = @overflowStopImpl := by
  funext w
  unfold overflowStop overflowStopImpl SeLe4n.Model.MessageInfo.decode
  simp only [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have h7 : (7 : UInt64).toNat % 64 = 7 := rfl
  have h9 : (9 : UInt64).toNat % 64 = 9 := rfl
  have h7f : (0x7F : UInt64).toNat = 0x7F := rfl
  have h3 : (0x3 : UInt64).toNat = 0x3 := rfl
  rw [h7, h9, h7f, h3]
  by_cases hc : (decide ((w.toNat &&& 0x7F) ≤ maxMessageRegisters) &&
      decide ((w.toNat >>> 7 &&& 0x3) ≤ SeLe4n.Model.maxExtraCaps) &&
      decide ((w.toNat >>> 9) ≤ SeLe4n.Model.MessageInfo.maxLabel)) = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]

/-- **WS-BP BP7.8: the addresses of the overflow words a syscall will read** —
the caller's slots `0 .. overflow` that the shared resolver answers, where
`overflow` is how many message registers past the four inline ones the
`MessageInfo` word asks for.  A slot the resolver refuses is not read, and the
decode then fails it closed exactly as before (`.invalidMessageInfo`). -/
def callerOverflowAddrs (st : SystemState) (tid : ThreadId) (msgInfo : UInt64) : List PAddr :=
  match st.getTcb? tid with
  | some tcb =>
      (List.range (overflowStop msgInfo)).filterMap (fun i => ipcBufferSlotPAddr? st tcb i false)
  | none => []

/-- **WS-BP BP7.8: the decode reads what RAM holds** at the words the entry
read — applied in the atomic step before the decode, so the decode reads the
sender's message registers rather than the model's stale copy of its frame.

WS-ZA ZA5.2: the words are the `n` pairs of `bytes` (the core's entry-word
buffer on hardware), and they **replace** the machine's
(`MachineState.entryWordBytes`), which the read consults ahead of `memory`
(`userWordAt`); an entry that read none holds none.  The entry wrote them into
`memory` until then, and `memory` is a function: each write wrapped it in
another closure that the committed state kept, so every syscall carrying
overflow registers grew the kernel heap for good.  Now `memory` is left as it
was (`syncUserWords_memory`) and the committed state holds no words
(`clearUserWords`). -/
def syncUserWords (st : SystemState) (bytes : ByteArray) (n : Nat) : SystemState :=
  if n = 0 then
    { st with machine := { st.machine with entryWordBytes := ByteArray.empty, entryWordCount := 0 } }
  else
    { st with machine := { st.machine with entryWordBytes := bytes, entryWordCount := n } }

/-- **WS-ZA ZA5.2: the committed state holds no entry words** — what the syscall
entry applies to the step's result, so the core's buffer, which the next entry
on that core rewrites, is never read after the entry that filled it. -/
@[inline] def clearUserWords (st : SystemState) : SystemState :=
  syncUserWords st ByteArray.empty 0

theorem byteArray_eq_empty_of_size {b : ByteArray} (h : b.size = 0) : b = ByteArray.empty := by
  cases b with
  | mk data =>
    have : data = #[] := Array.eq_empty_of_size_eq_zero (by simpa [ByteArray.size] using h)
    subst this
    rfl

/-- The compiled `syncUserWords`: an entry with no words over a state holding
none writes nothing, so the common syscall rebuilds no record. -/
@[inline] def syncUserWordsImpl (st : SystemState) (bytes : ByteArray) (n : Nat) :
    SystemState :=
  if n = 0 ∧ st.machine.entryWordCount = 0 ∧ st.machine.entryWordBytes.size = 0 then st
  else if n = 0 then
    { st with machine := { st.machine with entryWordBytes := ByteArray.empty, entryWordCount := 0 } }
  else
    { st with machine := { st.machine with entryWordBytes := bytes, entryWordCount := n } }

@[csimp] theorem syncUserWords_eq_impl : @syncUserWords = @syncUserWordsImpl := by
  funext st bytes n
  unfold syncUserWords syncUserWordsImpl
  by_cases hN : n = 0
  · subst hN
    by_cases hS : st.machine.entryWordCount = 0 ∧ st.machine.entryWordBytes.size = 0
    · simp only [hS, and_self, ite_true]
      obtain ⟨hC, hB⟩ := hS
      have hB' := byteArray_eq_empty_of_size hB
      cases st with
      | mk machine =>
        cases machine
        simp_all
    · simp only [hS, and_false, ite_false, ite_true]
  · simp only [hN, false_and, ite_false]

@[simp] theorem syncUserWords_objects (st : SystemState) (bytes : ByteArray) (n : Nat) :
    (syncUserWords st bytes n).objects = st.objects := by
  unfold syncUserWords; split <;> rfl

@[simp] theorem syncUserWords_scheduler (st : SystemState) (bytes : ByteArray) (n : Nat) :
    (syncUserWords st bytes n).scheduler = st.scheduler := by
  unfold syncUserWords; split <;> rfl

/-- **WS-ZA ZA5.2: the sync leaves memory as it was** — the property whose
absence let a thread grow the kernel heap without bound. -/
@[simp] theorem syncUserWords_memory (st : SystemState) (bytes : ByteArray) (n : Nat) :
    (syncUserWords st bytes n).machine.memory = st.machine.memory := by
  unfold syncUserWords; split <;> rfl

/-- The sync touches nothing but the entry's words. -/
theorem syncUserWords_eq_words (st : SystemState) (bytes : ByteArray) (n : Nat) :
    ∃ b c, syncUserWords st bytes n =
      { st with machine := { st.machine with entryWordBytes := b, entryWordCount := c } } := by
  unfold syncUserWords; split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- Syncing twice keeps only the second entry's words: nothing accumulates. -/
@[simp] theorem syncUserWords_syncUserWords (st : SystemState)
    (bytes bytes' : ByteArray) (n n' : Nat) :
    syncUserWords (syncUserWords st bytes n) bytes' n' = syncUserWords st bytes' n' := by
  unfold syncUserWords
  by_cases h : n = 0 <;> by_cases h' : n' = 0 <;> simp [h, h']

/-- **WS-BP BP7.8: the sync is what the decode reads.**  After syncing words
whose first pair is `w` at the address the resolver answers for slot `idx`,
the decode's read of that slot is `w`. -/
theorem ipcBufferReadMr_syncUserWord (st : SystemState) (tid : ThreadId)
    (tcb : SeLe4n.Model.TCB) (idx : Nat) (pa : PAddr) (w : UInt64)
    (bytes : ByteArray) (n : Nat)
    (hTcb : st.getTcb? tid = some tcb)
    (hPa : ipcBufferSlotPAddr? st tcb idx false = some pa)
    (hN : 0 < n) (hAddr : pairAddr bytes 0 = pa.toNat) (hWord : pairWord bytes 0 = w) :
    ipcBufferReadMr (syncUserWords st bytes n) tid idx = .ok w := by
  obtain ⟨b, c, hEq⟩ := syncUserWords_eq_words st bytes n
  have hTcb' : (syncUserWords st bytes n).getTcb? tid = some tcb := by
    rw [hEq]; simpa [SystemState.getTcb?] using hTcb
  have hPa' : ipcBufferSlotPAddr? (syncUserWords st bytes n) tcb idx false = some pa := by
    rw [hEq]; simpa [ipcBufferSlotPAddr?, SystemState.getVSpaceRoot?] using hPa
  rw [ipcBufferReadMr_of_slotPAddr? _ tid tcb idx false pa hTcb' hPa']
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [syncUserWords, Nat.add_one_ne_zero, ↓reduceIte, userWordAt, syncedWordAt,
    syncedWordFrom, hAddr, hWord]

/-- WS-ZA ZA5.2: the pairs `entries` laid out as an entry-word buffer — what the
HAL's capture writes, built in Lean for the host suites. -/
def encodeWordPairs (entries : List (PAddr × UInt64)) : ByteArray :=
  entries.foldl (fun b (pa, w) =>
    let le (x : UInt64) (acc : ByteArray) : ByteArray :=
      (List.range 8).foldl (fun a j => a.push (x >>> (8 * j).toUInt64).toUInt8) acc
    le w (le pa.toNat.toUInt64 b)) ByteArray.empty

-- ============================================================================
-- `v0.36.47` audit — the overflow words cross the boundary in runs
-- ============================================================================

/-- The page the HAL bounds a run against: its `PAGE_BYTES`
(`rust/sele4n-hal/src/user_translation.rs`), the 4 KiB page `pageOffset` and
`ipcBufferSlotPage` already assume. -/
def wordRunPageBytes : Nat := 4096

/-- The addresses a run names, in order. -/
def expandRun (run : PAddr × Nat) : List PAddr :=
  (List.range run.2).map (fun i => PAddr.ofNat (run.1.toNat + 8 * i))

/-- The addresses a list of runs names, in order. -/
def expandRuns (runs : List (PAddr × Nat)) : List PAddr := runs.flatMap expandRun

theorem PAddr.ofNat_toNat (a : PAddr) : PAddr.ofNat a.toNat = a := rfl

/-- **WS-ZA ZA5.2: the first slot from `i` the resolver answers**, looking at
`k` slots, or `i + k` when none does.  A scalar answer, so the entry's run loop
builds nothing. -/
def nextResolvedSlot (st : SystemState) (tcb : SeLe4n.Model.TCB) : Nat → Nat → Nat
  | i, 0 => i
  | i, k + 1 =>
    match ipcBufferSlotPAddr? st tcb i false with
    | some _ => i
    | none => nextResolvedSlot st tcb (i + 1) k

/-- **WS-ZA ZA5.2: how long a run starting at `base` grows**: from `len` words,
each following slot (from `i`, `k` of them) that the resolver answers at the
next word of `base`'s page extends it, and the first that does not ends it. -/
def runExtent (st : SystemState) (tcb : SeLe4n.Model.TCB) (base : Nat) :
    Nat → Nat → Nat → Nat
  | _, len, 0 => len
  | i, len, k + 1 =>
    match ipcBufferSlotPAddr? st tcb i false with
    | some pa =>
      if pa.toNat = base + 8 * len ∧ pa.toNat / wordRunPageBytes = base / wordRunPageBytes then
        runExtent st tcb base (i + 1) (len + 1) k
      else len
    | none => len

/-- The runs of the slots from `i` below `stop` (`fuel` bounds the recursion;
`stop` suffices, since every run consumes a slot). -/
def overflowRunsFrom (st : SystemState) (tcb : SeLe4n.Model.TCB) (stop : Nat) :
    Nat → Nat → List (PAddr × Nat)
  | 0, _ => []
  | fuel + 1, i =>
    let s := nextResolvedSlot st tcb i (stop - i)
    if s < stop then
      match ipcBufferSlotPAddr? st tcb s false with
      | some pa =>
        let len := runExtent st tcb pa.toNat (s + 1) 1 (stop - (s + 1))
        (pa, len) :: overflowRunsFrom st tcb stop fuel (s + len)
      | none => []
    else []

/-- **WS-ZA ZA5.2 (the `v0.36.47` audit's runs, planned without a list): the
contiguous runs of a thread's overflow slots `0 .. stop`** that the resolver
answers — `(base, n)` names the `n` words `base, base + 8, …`, a run is
extended only by the next word of the same page, and the HAL reads each run
with one translation.  The entry's capture walks exactly this recursion
(`SyscallDispatchEntry.captureOverflowRuns`); here it is a list so the two
facts below can be stated: the runs are the slots the decode reads
(`expandRuns_overflowRuns`), and no run leaves its page
(`overflowRuns_within_page`). -/
def overflowRuns (st : SystemState) (tcb : SeLe4n.Model.TCB) (stop : Nat) :
    List (PAddr × Nat) :=
  overflowRunsFrom st tcb stop stop 0

/-- What `nextResolvedSlot` skips resolves to nothing. -/
theorem nextResolvedSlot_spec (st : SystemState) (tcb : SeLe4n.Model.TCB) :
    ∀ (k i : Nat), i ≤ nextResolvedSlot st tcb i k ∧ nextResolvedSlot st tcb i k ≤ i + k ∧
      (List.range' i k).filterMap (fun j => ipcBufferSlotPAddr? st tcb j false) =
        (List.range' (nextResolvedSlot st tcb i k) (i + k - nextResolvedSlot st tcb i k)).filterMap
          (fun j => ipcBufferSlotPAddr? st tcb j false)
  | 0, i => by simp [nextResolvedSlot]
  | k + 1, i => by
    unfold nextResolvedSlot
    split
    · rename_i pa hPa
      refine ⟨Nat.le_refl _, by omega, ?_⟩
      rw [show i + (k + 1) - i = k + 1 by omega]
    · rename_i hNone
      obtain ⟨h1, h2, h3⟩ := nextResolvedSlot_spec st tcb k (i + 1)
      refine ⟨by omega, by omega, ?_⟩
      rw [List.range'_succ, List.filterMap_cons, hNone, h3,
        show i + 1 + k = i + (k + 1) by omega]

/-- The slot `nextResolvedSlot` stops at, short of its bound, resolves. -/
theorem nextResolvedSlot_resolves (st : SystemState) (tcb : SeLe4n.Model.TCB) :
    ∀ (k i : Nat), nextResolvedSlot st tcb i k < i + k →
      ∃ pa, ipcBufferSlotPAddr? st tcb (nextResolvedSlot st tcb i k) false = some pa
  | 0, i, h => by simp [nextResolvedSlot] at h
  | k + 1, i, h => by
    unfold nextResolvedSlot at h ⊢
    split
    · rename_i pa hPa; exact ⟨pa, hPa⟩
    · rename_i hNone
      rw [hNone] at h
      exact nextResolvedSlot_resolves st tcb k (i + 1) (by simp only at h; omega)
/-- What `runExtent` consumes: the slots it takes resolve, in order, to the
words after `base`'s `len`-th, all in `base`'s page; what it leaves is the
rest of the slots. -/
theorem runExtent_spec (st : SystemState) (tcb : SeLe4n.Model.TCB) (base : Nat) :
    ∀ (k i len : Nat), len ≤ runExtent st tcb base i len k ∧
      runExtent st tcb base i len k ≤ len + k ∧
      (List.range' i k).filterMap (fun j => ipcBufferSlotPAddr? st tcb j false) =
        (List.range (runExtent st tcb base i len k - len)).map
            (fun j => PAddr.ofNat (base + 8 * (len + j))) ++
          (List.range' (i + (runExtent st tcb base i len k - len))
              (k - (runExtent st tcb base i len k - len))).filterMap
            (fun j => ipcBufferSlotPAddr? st tcb j false) ∧
      ∀ j, j < runExtent st tcb base i len k - len →
        (base + 8 * (len + j)) / wordRunPageBytes = base / wordRunPageBytes
  | 0, i, len => by simp [runExtent]
  | k + 1, i, len => by
    unfold runExtent
    split
    · rename_i pa hPa
      split
      · rename_i hNext
        obtain ⟨h1, h2, h3, h4⟩ := runExtent_spec st tcb base k (i + 1) (len + 1)
        generalize hr : runExtent st tcb base (i + 1) (len + 1) k = r at h1 h2 h3 h4
        obtain ⟨m, rfl⟩ : ∃ m, r = len + 1 + m := ⟨r - (len + 1), by omega⟩
        refine ⟨by omega, by omega, ?_, ?_⟩
        · rw [show len + 1 + m - len = m + 1 by omega, List.range'_succ, List.filterMap_cons, hPa,
            show len + 1 + m - (len + 1) = m by omega] at *
          rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append, h3,
            show i + (m + 1) = i + 1 + m by omega, show k + 1 - (m + 1) = k - m by omega]
          dsimp only
          have hpa : pa = PAddr.ofNat (base + 8 * (len + 0)) := by
            rw [← PAddr.ofNat_toNat pa, hNext.1, Nat.add_zero]
          rw [← hpa]
          congr 2
          apply List.map_congr_left
          intro j _
          simp only [Function.comp]
          congr 1
          omega
        · rw [show len + 1 + m - len = m + 1 by omega] at *
          rw [show len + 1 + m - (len + 1) = m by omega] at h4
          intro j hj
          cases j with
          | zero =>
            simp only [Nat.add_zero]
            rw [← hNext.1]
            exact hNext.2
          | succ j =>
            have := h4 j (by omega)
            rw [show len + (j + 1) = len + 1 + j by omega]
            exact this
      · refine ⟨Nat.le_refl _, by omega, ?_, by simp⟩
        simp
    · refine ⟨Nat.le_refl _, by omega, ?_, by simp⟩
      simp

/-- **The runs are the slots the decode reads**: from slot `i`, with enough
fuel, the runs name exactly the slots below `stop` the resolver answers, in
order. -/
theorem expandRuns_overflowRunsFrom (st : SystemState) (tcb : SeLe4n.Model.TCB) (stop : Nat) :
    ∀ (fuel i : Nat), stop - i ≤ fuel →
      expandRuns (overflowRunsFrom st tcb stop fuel i) =
        (List.range' i (stop - i)).filterMap (fun j => ipcBufferSlotPAddr? st tcb j false)
  | 0, i, h => by
    simp only [overflowRunsFrom, expandRuns, List.flatMap_nil]
    rw [show stop - i = 0 by omega]; rfl
  | fuel + 1, i, h => by
    obtain ⟨n1, n2, n3⟩ := nextResolvedSlot_spec st tcb (stop - i) i
    simp only [overflowRunsFrom]
    generalize hs : nextResolvedSlot st tcb i (stop - i) = s at n1 n2 n3
    split
    · rename_i hLt
      obtain ⟨pa, hPa⟩ := nextResolvedSlot_resolves st tcb (stop - i) i (by omega)
      rw [hs] at hPa
      rw [hPa]
      dsimp only
      obtain ⟨r1, r2, r3, -⟩ := runExtent_spec st tcb pa.toNat (stop - (s + 1)) (s + 1) 1
      generalize hlen : runExtent st tcb pa.toNat (s + 1) 1 (stop - (s + 1)) = len at r1 r2 r3
      have ih := expandRuns_overflowRunsFrom st tcb stop fuel (s + len) (by omega)
      simp only [expandRuns, List.flatMap_cons] at ih ⊢
      rw [ih, n3, show i + (stop - i) - s = (stop - (s + 1)) + 1 by omega, List.range'_succ,
        List.filterMap_cons, hPa, r3]
      obtain ⟨m, rfl⟩ : ∃ m, len = m + 1 := ⟨len - 1, by omega⟩
      simp only [expandRun, List.range_succ_eq_map, List.map_cons, List.map_map,
        Nat.mul_zero, Nat.add_zero, PAddr.ofNat_toNat, List.cons_append,
        show m + 1 - 1 = m by omega]
      congr 1
      rw [show s + 1 + m = s + (m + 1) by omega,
        show stop - (s + 1) - m = stop - (s + (m + 1)) by omega, List.append_cancel_right_eq]
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      congr 1
      omega
    · rename_i hGe
      simp only [expandRuns, List.flatMap_nil]
      rw [n3, show i + (stop - i) - s = 0 by omega]
      rfl

/-- **The runs are the slots the decode reads**: the overflow runs of a
thread's slots `0 .. stop` name exactly the slots the resolver answers, in
order — the words `callerOverflowAddrs` names and the decode reads. -/
theorem expandRuns_overflowRuns (st : SystemState) (tcb : SeLe4n.Model.TCB) (stop : Nat) :
    expandRuns (overflowRuns st tcb stop) =
      (List.range stop).filterMap (fun j => ipcBufferSlotPAddr? st tcb j false) := by
  rw [overflowRuns, expandRuns_overflowRunsFrom st tcb stop stop 0 (by omega),
    List.range_eq_range', Nat.sub_zero]

/-- Each run of `overflowRunsFrom` starts at an answered slot and stays in its
page: `base % 4096 + 8 · n ≤ 4096`, with `n ≥ 1`. -/
theorem overflowRunsFrom_within_page (st : SystemState) (tcb : SeLe4n.Model.TCB) (stop : Nat) :
    ∀ (fuel i : Nat) (run : PAddr × Nat), run ∈ overflowRunsFrom st tcb stop fuel i →
      0 < run.2 ∧ run.1.toNat % wordRunPageBytes + 8 * run.2 ≤ wordRunPageBytes
  | 0, _, _, h => by simp [overflowRunsFrom] at h
  | fuel + 1, i, run, h => by
    simp only [overflowRunsFrom] at h
    split at h
    · split at h
      · rename_i pa hPa
        rcases List.mem_cons.mp h with rfl | hMem
        · obtain ⟨r1, r2, -, r4⟩ := runExtent_spec st tcb pa.toNat
            (stop - (nextResolvedSlot st tcb i (stop - i) + 1))
            (nextResolvedSlot st tcb i (stop - i) + 1) 1
          generalize runExtent st tcb pa.toNat (nextResolvedSlot st tcb i (stop - i) + 1) 1
            (stop - (nextResolvedSlot st tcb i (stop - i) + 1)) = len at r1 r2 r4
          have hAl := ipcBufferSlotPAddr?_aligned st tcb _ false pa hPa
          refine ⟨by omega, ?_⟩
          by_cases hOne : len = 1
          · subst hOne
            simp only [wordRunPageBytes] at hAl ⊢
            omega
          · have hLast := r4 (len - 2) (by omega)
            simp only [wordRunPageBytes] at hLast hAl ⊢
            rw [show 1 + (len - 2) = len - 1 by omega] at hLast
            omega
        · exact overflowRunsFrom_within_page st tcb stop fuel _ run hMem
      · simp at h
    · simp at h

/-- **The kernel never asks the HAL for a run it refuses**: every overflow run
lies within its page — `base % 4096 + 8 · n ≤ 4096`, the bound
`user_word_run_admissible` checks — and names at least one word. -/
theorem overflowRuns_within_page (st : SystemState) (tcb : SeLe4n.Model.TCB) (stop : Nat)
    (run : PAddr × Nat) (h : run ∈ overflowRuns st tcb stop) :
    0 < run.2 ∧ run.1.toNat % wordRunPageBytes + 8 * run.2 ≤ wordRunPageBytes :=
  overflowRunsFrom_within_page st tcb stop stop 0 run h

end SeLe4n.Kernel.Architecture.IpcBufferRead
