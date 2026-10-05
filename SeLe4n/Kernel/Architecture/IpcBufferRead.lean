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
def ipcBufferSlotPAddr? (st : SystemState) (tcb : SeLe4n.Model.TCB) (idx : Nat)
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
    ipcBufferReadMr st tid idx
      = .ok (SeLe4n.Kernel.Architecture.readUInt64 st.machine.memory pa) := by
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

/-- **WS-BP BP7.8: the model learns a word the thread holds in RAM.**  Writes
only `machine.memory`; every object, the scheduler and every ledger are
untouched (`syncUserWord_objects`, `_scheduler`). -/
def syncUserWord (st : SystemState) (pa : PAddr) (w : UInt64) : SystemState :=
  { st with machine :=
      { st.machine with memory := SeLe4n.Kernel.Architecture.writeUInt64 st.machine.memory pa w } }

@[simp] theorem syncUserWord_objects (st : SystemState) (pa : PAddr) (w : UInt64) :
    (syncUserWord st pa w).objects = st.objects := rfl
@[simp] theorem syncUserWord_scheduler (st : SystemState) (pa : PAddr) (w : UInt64) :
    (syncUserWord st pa w).scheduler = st.scheduler := rfl
@[simp] theorem syncUserWord_memory (st : SystemState) (pa : PAddr) (w : UInt64) :
    (syncUserWord st pa w).machine.memory
      = SeLe4n.Kernel.Architecture.writeUInt64 st.machine.memory pa w := rfl

/-- **WS-BP BP7.8: the addresses of the overflow words a syscall will read** —
the caller's slots `0 .. overflow` that the shared resolver answers, where
`overflow` is how many message registers past the four inline ones the
`MessageInfo` word asks for.  A slot the resolver refuses is not read, and the
decode then fails it closed exactly as before (`.invalidMessageInfo`). -/
def callerOverflowAddrs (st : SystemState) (tid : ThreadId) (msgInfo : UInt64) : List PAddr :=
  match st.getTcb? tid, SeLe4n.Model.MessageInfo.decode msgInfo.toNat with
  | some tcb, some mi =>
      (List.range (min (mi.length - 4) maxOverflowSlots)).filterMap
        (fun i => ipcBufferSlotPAddr? st tcb i false)
  | _, _ => []

/-- **WS-BP BP7.8: make the model's memory hold what RAM holds** at the words
the entry read — applied in the atomic step before the decode, so the decode
reads the sender's message registers rather than the model's stale copy of
its frame. -/
def syncUserWords (st : SystemState) (words : List (PAddr × UInt64)) : SystemState :=
  words.foldl (fun s pw => syncUserWord s pw.1 pw.2) st

@[simp] theorem syncUserWords_objects (st : SystemState) (words : List (PAddr × UInt64)) :
    (syncUserWords st words).objects = st.objects := by
  induction words generalizing st with
  | nil => rfl
  | cons pw rest ih => simp [syncUserWords, List.foldl] at ih ⊢; exact ih _

@[simp] theorem syncUserWords_scheduler (st : SystemState) (words : List (PAddr × UInt64)) :
    (syncUserWords st words).scheduler = st.scheduler := by
  induction words generalizing st with
  | nil => rfl
  | cons pw rest ih => simp [syncUserWords, List.foldl] at ih ⊢; exact ih _

/-- **WS-BP BP7.8: the sync is what the decode reads.**  After syncing the word
`w` at the address the resolver answers for slot `idx`, the decode's read of
that slot is `w`. -/
theorem ipcBufferReadMr_syncUserWord (st : SystemState) (tid : ThreadId)
    (tcb : SeLe4n.Model.TCB) (idx : Nat) (pa : PAddr) (w : UInt64)
    (hTcb : st.getTcb? tid = some tcb)
    (hPa : ipcBufferSlotPAddr? st tcb idx false = some pa) :
    ipcBufferReadMr (syncUserWord st pa w) tid idx = .ok w := by
  have hTcb' : (syncUserWord st pa w).getTcb? tid = some tcb := by
    simpa [SystemState.getTcb?, syncUserWord] using hTcb
  have hPa' : ipcBufferSlotPAddr? (syncUserWord st pa w) tcb idx false = some pa := by
    simpa [ipcBufferSlotPAddr?, SystemState.getVSpaceRoot?, syncUserWord] using hPa
  rw [ipcBufferReadMr_of_slotPAddr? _ tid tcb idx false pa hTcb' hPa', syncUserWord_memory,
    SeLe4n.Kernel.Architecture.readUInt64_writeUInt64]

-- ============================================================================
-- `v0.36.47` audit — the overflow words cross the boundary in runs
-- ============================================================================

/-- The page the HAL bounds a run against: its `PAGE_BYTES`
(`rust/sele4n-hal/src/user_translation.rs`), the 4 KiB page `pageOffset` and
`ipcBufferSlotPage` already assume. -/
def wordRunPageBytes : Nat := 4096

/-- **The contiguous runs of a list of word addresses** (`v0.36.47` audit):
`(base, n)` names the `n` eight-byte words `base, base + 8, …`, and a run is
extended only by the next address of the same page, so every run lies in one
page and the HAL translates it once.  The sender's overflow slots are such a
list (`callerOverflowAddrs`) — consecutive words of a 512-byte-aligned buffer —
so on a buffer that does not straddle a page boundary the whole message is one
run, and on one that does it is two.  Nothing is dropped and nothing is
reordered: `expandRuns_wordRuns` says the runs are the list. -/
def wordRuns : List PAddr → List (PAddr × Nat)
  | [] => []
  | pa :: rest =>
    match wordRuns rest with
    | (base, n) :: runs =>
        if base.toNat = pa.toNat + 8 ∧
            pa.toNat / wordRunPageBytes = base.toNat / wordRunPageBytes then
          (pa, n + 1) :: runs
        else (pa, 1) :: (base, n) :: runs
    | [] => [(pa, 1)]

/-- The addresses a run names, in order. -/
def expandRun (run : PAddr × Nat) : List PAddr :=
  (List.range run.2).map (fun i => PAddr.ofNat (run.1.toNat + 8 * i))

/-- The addresses a list of runs names, in order. -/
def expandRuns (runs : List (PAddr × Nat)) : List PAddr := runs.flatMap expandRun

theorem PAddr.ofNat_toNat (a : PAddr) : PAddr.ofNat a.toNat = a := rfl

/-- A run grown by its predecessor word names that word and then the run. -/
theorem expandRun_succ (pa base : PAddr) (n : Nat) (h : base.toNat = pa.toNat + 8) :
    expandRun (pa, n + 1) = pa :: expandRun (base, n) := by
  simp only [expandRun, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero,
    Nat.add_zero, PAddr.ofNat_toNat, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, h]
  congr 1
  omega

/-- **The runs are the list**: expanding the runs of `addrs` gives back `addrs`,
so the batch reads exactly the words the per-word loop read, in the same
order, and `syncUserWords` receives the same `(address, word)` pairs. -/
theorem expandRuns_wordRuns : ∀ addrs : List PAddr, expandRuns (wordRuns addrs) = addrs
  | [] => rfl
  | pa :: rest => by
    have ih := expandRuns_wordRuns rest
    simp only [wordRuns]
    split
    · rename_i base n runs hRuns
      rw [hRuns] at ih
      split
      · rename_i hNext
        simp only [expandRuns, List.flatMap_cons] at ih ⊢
        rw [expandRun_succ pa base n hNext.1, List.cons_append, ih]
      · simp only [expandRuns, List.flatMap_cons] at ih ⊢
        rw [ih]
        rfl
    · rename_i hRuns
      rw [hRuns] at ih
      simp only [expandRuns, List.flatMap_nil] at ih
      subst ih
      rfl

/-- Every run names at least one word. -/
theorem wordRuns_pos : ∀ (addrs : List PAddr) (run : PAddr × Nat),
    run ∈ wordRuns addrs → 0 < run.2
  | [], _, h => by simp [wordRuns] at h
  | pa :: rest, run, h => by
    simp only [wordRuns] at h
    split at h
    · rename_i base n runs hRuns
      split at h
      · rcases List.mem_cons.mp h with rfl | hMem
        · exact Nat.succ_pos _
        · exact wordRuns_pos rest run (hRuns ▸ List.mem_cons_of_mem _ hMem)
      · rcases List.mem_cons.mp h with rfl | hMem
        · exact Nat.one_pos
        · exact wordRuns_pos rest run (hRuns ▸ hMem)
    · rcases List.mem_singleton.mp h with rfl
      exact Nat.one_pos

/-- **Every word of a run is in the run's page**: a run is only ever extended
by the next word of the same page. -/
theorem wordRuns_same_page : ∀ (addrs : List PAddr) (run : PAddr × Nat),
    run ∈ wordRuns addrs → ∀ a ∈ expandRun run,
      a.toNat / wordRunPageBytes = run.1.toNat / wordRunPageBytes
  | [], _, h => by simp [wordRuns] at h
  | pa :: rest, run, h => by
    simp only [wordRuns] at h
    split at h
    · rename_i base n runs hRuns
      split at h
      · rename_i hNext
        rcases List.mem_cons.mp h with rfl | hMem
        · intro a ha
          rw [expandRun_succ pa base n hNext.1] at ha
          rcases List.mem_cons.mp ha with rfl | ha'
          · rfl
          · have := wordRuns_same_page rest (base, n) (hRuns ▸ List.mem_cons_self) a ha'
            simp only at this ⊢
            rw [this, hNext.2]
        · exact wordRuns_same_page rest run (hRuns ▸ List.mem_cons_of_mem _ hMem)
      · rcases List.mem_cons.mp h with rfl | hMem
        · intro a ha
          simp only [expandRun, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
            Nat.add_zero, PAddr.ofNat_toNat, List.mem_singleton] at ha
          rw [ha]
        · exact wordRuns_same_page rest run (hRuns ▸ hMem)
    · rcases List.mem_singleton.mp h with rfl
      intro a ha
      simp only [expandRun, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
        Nat.add_zero, PAddr.ofNat_toNat, List.mem_singleton] at ha
      rw [ha]

/-- The words a run names are words of the list. -/
theorem mem_of_mem_expandRun_wordRuns (addrs : List PAddr) (run : PAddr × Nat)
    (hRun : run ∈ wordRuns addrs) (a : PAddr) (ha : a ∈ expandRun run) : a ∈ addrs := by
  rw [← expandRuns_wordRuns addrs]
  simp only [expandRuns, List.mem_flatMap]
  exact ⟨run, hRun, ha⟩

/-- **The kernel never asks the HAL for a run it refuses**: over eight-byte
aligned words, every run of `wordRuns` lies within its page —
`base % 4096 + 8 · n ≤ 4096`, the bound `user_word_run_admissible` checks. -/
theorem wordRuns_within_page (addrs : List PAddr)
    (hAligned : ∀ a ∈ addrs, a.toNat % 8 = 0) (run : PAddr × Nat)
    (hRun : run ∈ wordRuns addrs) :
    run.1.toNat % wordRunPageBytes + 8 * run.2 ≤ wordRunPageBytes := by
  obtain ⟨base, n⟩ := run
  have hPos : 0 < n := wordRuns_pos addrs (base, n) hRun
  -- The run's last word is a word of the list: aligned, and in `base`'s page.
  have hLast : PAddr.ofNat (base.toNat + 8 * (n - 1)) ∈ expandRun (base, n) := by
    simp only [expandRun, List.mem_map, List.mem_range]
    exact ⟨n - 1, by omega, rfl⟩
  have hAl := hAligned _ (mem_of_mem_expandRun_wordRuns addrs (base, n) hRun _ hLast)
  have hPage := wordRuns_same_page addrs (base, n) hRun _ hLast
  simp only [PAddr.toNat, PAddr.ofNat, wordRunPageBytes] at hAl hPage ⊢
  omega

/-- **The `count` little-endian words a batch read answered** (`v0.36.47`
audit), or nothing when the HAL answered any other number of bytes.  A
`ByteArray` is one scalar allocation of `8 · count` bytes — no word is boxed on
the way over, and the decode reads unboxed bytes — which is why the HAL answers
in this form rather than an `Array UInt64` of heap cells. -/
def wordsOfBytes (count : Nat) (bytes : ByteArray) : Option (List UInt64) :=
  if bytes.size = 8 * count then
    some ((List.range count).map fun i =>
      (List.range 8).foldl
        (fun acc j => acc ||| ((bytes[8 * i + j]!).toUInt64 <<< (8 * j).toUInt64)) 0)
  else none

/-- A decoded batch has exactly the run's count of words. -/
theorem wordsOfBytes_length (count : Nat) (bytes : ByteArray) (ws : List UInt64)
    (h : wordsOfBytes count bytes = some ws) : ws.length = count := by
  unfold wordsOfBytes at h
  split at h
  · cases h; simp
  · cases h

/-- The batches of a list of runs, decoded run by run and concatenated — or
nothing when any batch is not its run's `8 · n` bytes, or the HAL answered a
different number of batches than there are runs. -/
def wordsOfBatches : List (PAddr × Nat) → List ByteArray → Option (List UInt64)
  | [], [] => some []
  | (_, n) :: runs, bytes :: rest => do
      let ws ← wordsOfBytes n bytes
      let more ← wordsOfBatches runs rest
      pure (ws ++ more)
  | _, _ => none

/-- A decoded batch list has one word per run word. -/
theorem wordsOfBatches_length : ∀ (runs : List (PAddr × Nat)) (batches : List ByteArray)
    (ws : List UInt64), wordsOfBatches runs batches = some ws →
      ws.length = (expandRuns runs).length
  | [], [], ws, h => by
      simp only [wordsOfBatches, Option.some.injEq] at h; subst h; rfl
  | (_, n) :: runs, bytes :: rest, ws, h => by
      simp only [wordsOfBatches, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨w, hw, more, hmore, rfl⟩ := h
      simp only [expandRuns, List.flatMap_cons, List.length_append, List.length_append,
        wordsOfBytes_length n bytes w hw,
        wordsOfBatches_length runs rest more hmore, expandRun, List.length_map,
        List.length_range]
  | [], _ :: _, _, h => by simp [wordsOfBatches] at h
  | _ :: _, [], _, h => by simp [wordsOfBatches] at h

end SeLe4n.Kernel.Architecture.IpcBufferRead
