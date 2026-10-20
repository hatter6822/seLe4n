-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Kernel.Architecture.CacheInvalidation
import SeLe4n.Kernel.Architecture.LittleEndianWords
import SeLe4n.Model.Erased

/-!
# WS-BP BP7.2 — the physical writes a committed transition owes

Kernel transitions are pure functions of `SystemState`, so a transition that
changes an address space's translation — a mapping, an installed table, a page
carved for a thread — describes the change and does not perform it.  The
hardware walker reads **physical memory**, so each such change owes a store to
RAM: a descriptor in a table page, or a scrub of a page a thread is about to be
handed.  `PhysicalWrite` is that store, recorded in the order the transition
made the change (`SystemState.pendingPhysicalWrites`) and emitted by the syscall
seam after the commit and **before** the shootdown round, so a translation the
transition retired is gone from memory before any core is told to drop it from
its TLB.

This is the ledger shape `pendingIcacheMaintenance` established (SM7.D.1), and
it is extracted to this pure module for that ledger's reason: a state-layer field
must not pull the architecture layer's import closure.

## Encoding contract

The tag/operand encoding **must** stay in lockstep with
`rust/sele4n-hal/src/user_translation.rs::apply_physical_write`:

  tag 0 = zero one 4 KiB page at `addr`, then clean it to the Point of
          Unification and invalidate every instruction cache in the domain
          (`PhysicalWrite.icacheMaintenance`)  (`value` ignored)
  tag 1 = store the **level-3 page** descriptor `value` at `addr`
  tag 2 = invalidate every translation tagged `addr` as an ASID (`value` ignored)
  tag 3 = store the user word `value` at `addr`, in a thread's RAM page (WS-BP BP7.8)
  tag 4 = store the **table** descriptor `value` at `addr`, an entry of a level
          0–2 table page (PR #904, `v0.36.41`)

The two descriptor tags are distinct because the walker reads a descriptor by
the **level** of the table it sits in, and bits `[1:0] = 0b11` mean a page at
level 3 and a table at levels 0–2.  The HAL validates what a descriptor
*says* — a page's output address is a thread's frame or the device window, a
table's is a thread table page — and it can do that only if it knows which
reading the walker will apply.
-/

namespace SeLe4n.Kernel.Architecture

/-- **WS-BP BP7.2: one physical write a committed transition owes.** -/
inductive PhysicalWrite where
  /-- Zero the 4 KiB page at `base` — a page carved for a thread (a frame, a
      table, an address space's top-level table), scrubbed before any
      capability to it exists.  The model performs the same write on
      `MachineState.memory` (`zeroMemoryRange`). -/
  | zeroPage (base : SeLe4n.PAddr)
  /-- Store the 64-bit **level-3 page** descriptor `value` at `entry`, the
      address of one entry of a level-3 table page — a thread's mapping, or its
      clear (`0`). -/
  | storeDescriptor (entry : SeLe4n.PAddr) (value : UInt64)
  /-- Invalidate every translation cached under `asid`, on every PE — owed
      when a table descriptor is cleared (the walk caches intermediate levels,
      and a leaf TLBI names one address) and when an ASID is handed to a new
      address space. -/
  | invalidateAsid (asid : SeLe4n.ASID)
  /-- **WS-BP BP7.8**: store the 64-bit word `value` at `addr`, an eight-byte
      aligned address in a page of RAM a thread maps — a delivered message
      register past the four the return frame carries, written into the
      receiver's IPC buffer.  Distinct from `storeDescriptor` because the two
      name different memory: a descriptor lives in a table page (the boot pool
      or a carved table), a user word in a thread's own frame.  The HAL refuses
      a user word in the **pool**; a *carved* table is RAM past the kernel's
      extent like a frame, which the HAL cannot tell apart, so what keeps a
      user word out of it is this model — the address is resolved through the
      thread's own VSpace (`IpcBufferRead.ipcBufferSlotPAddr?`), which maps
      only frames, and carves are disjoint, so no mapped page is a table
      page. -/
  | storeUserWord (addr : SeLe4n.PAddr) (value : UInt64)
  /-- **PR #904 (`v0.36.41`)**: store the 64-bit **table** descriptor `value`
      at `entry`, the address of one entry of a level 0–2 table page — an
      installed table, or its clear (`0`).  Distinct from `storeDescriptor`
      because the walker reads a `0b11` descriptor as a table at these levels
      and as a page at level 3, and the HAL validates the output address
      against the reading the walker will apply. -/
  | storeTableDescriptor (entry : SeLe4n.PAddr) (value : UInt64)
  deriving Repr, DecidableEq

namespace PhysicalWrite

/-- The FFI tag (see the module's encoding contract). -/
@[inline] def tag : PhysicalWrite → UInt64
  | .zeroPage _ => 0
  | .storeDescriptor _ _ => 1
  | .invalidateAsid _ => 2
  | .storeUserWord _ _ => 3
  | .storeTableDescriptor _ _ => 4

/-- The FFI address operand. -/
@[inline] def addr : PhysicalWrite → UInt64
  | .zeroPage base => base.toNat.toUInt64
  | .storeDescriptor entry _ => entry.toNat.toUInt64
  | .invalidateAsid asid => asid.toNat.toUInt64
  | .storeUserWord a _ => a.toNat.toUInt64
  | .storeTableDescriptor entry _ => entry.toNat.toUInt64

/-- The FFI value operand. -/
@[inline] def value : PhysicalWrite → UInt64
  | .zeroPage _ => 0
  | .storeDescriptor _ v => v
  | .invalidateAsid _ => 0
  | .storeUserWord _ v => v
  | .storeTableDescriptor _ v => v

/-- Every tag is one of the five the HAL decodes. -/
theorem tag_le_four (w : PhysicalWrite) : w.tag ≤ 4 := by
  cases w <;> simp [tag]

/-- **WS-BP post-landing audit (`v0.36.32`): the instruction-cache maintenance a
physical write owes after its store**, which the HAL performs as the last step
of the write itself (`user_translation::apply_physical_write`, through
`user_translation::icache_maintenance`).

A zeroing is the only write that needs it.  It scrubs a page the kernel is about
to hand out — a frame a thread may map **executable** — through the kernel's
data cache, and an instruction fetch reads at the Point of Unification: until a
clean pushes the zeroes there, a fetch of the page can still read the bytes its
**previous owner** left (Cortex-A76 reports `CTR_EL0.IDC = 0`, so the data side
is not coherent with instruction fetch without that clean).  The operand is the
re-type's own (`ICacheInvalidation.cleanRangeIallu`, whose docstring states the
hazard for the in-place re-type's scrub and cites seL4's `clearMemory`): clean
the page, then invalidate every instruction cache in the domain, so no core
keeps a line of the page fetched before the carve.  The carve's scrub is a
kernel code-write site for that reason (`KernelCodeWriteSite.carveScrub`), and
this is its emission — carried by the write, so the clean can never be separated
from the zero it follows or reordered before it.

A descriptor store needs none (the table walk is coherent with the data cache
under `TCR_EL1`'s write-back, inner-shareable walk attributes), nor an ASID
invalidation, nor a user word (a thread's own buffer: a thread that executes
what it or the kernel wrote there unifies it itself, through
`.vspaceUnifyInstruction`). -/
def icacheMaintenance : PhysicalWrite → Option ICacheInvalidation
  | .zeroPage base => some (.cleanRangeIallu base SeLe4n.pageBytes)
  | .storeDescriptor _ _ => none
  | .invalidateAsid _ => none
  | .storeUserWord _ _ => none
  | .storeTableDescriptor _ _ => none

/-- **WS-BP post-landing audit (`v0.36.32`)**: a zeroing owes the clean of exactly
the page it zeroes, then the domain-wide invalidate. -/
@[simp] theorem icacheMaintenance_zeroPage (base : SeLe4n.PAddr) :
    (zeroPage base).icacheMaintenance = some (.cleanRangeIallu base SeLe4n.pageBytes) := rfl

/-- **WS-BP post-landing audit (`v0.36.32`)**: exactly the zeroings owe
instruction-cache maintenance. -/
theorem icacheMaintenance_isSome_iff (w : PhysicalWrite) :
    w.icacheMaintenance.isSome ↔ ∃ base, w = zeroPage base := by
  cases w <;> simp [icacheMaintenance]

/-- The three words the HAL is handed for a write. -/
@[inline] def words (w : PhysicalWrite) : UInt64 × UInt64 × UInt64 := (w.tag, w.addr, w.value)

end PhysicalWrite

-- ============================================================================
-- WS-ZA ZA5.4: the ledger as a word buffer
-- ============================================================================

/-- The bytes one ledger entry takes: its tag, address and value words. -/
def ledgerEntryBytes : Nat := 24

/-- The entries a ledger is made with room for; a transition that owes more
grows the buffer (an untyped reset's scrub of a large region). -/
def ledgerInitialEntries : Nat := 128

/-- The first `n` entries of a ledger buffer, as the HAL reads them. -/
def decodeLedger (b : ByteArray) : Nat → List (UInt64 × UInt64 × UInt64)
  | 0 => []
  | n + 1 => decodeLedger b n ++
      [(le64At b (ledgerEntryBytes * n), le64At b (ledgerEntryBytes * n + 8),
        le64At b (ledgerEntryBytes * n + 16))]

/-- Entry `i` of a ledger buffer: its tag, address and value words. -/
@[inline] def ledgerEntryAt (b : ByteArray) (i : Nat) : UInt64 × UInt64 × UInt64 :=
  (le64At b (ledgerEntryBytes * i), le64At b (ledgerEntryBytes * i + 8),
    le64At b (ledgerEntryBytes * i + 16))

/-- The `k` entries of a ledger buffer from entry `i`, in order. -/
def decodeLedgerFrom (b : ByteArray) : Nat → Nat → List (UInt64 × UInt64 × UInt64)
  | _, 0 => []
  | i, k + 1 => ledgerEntryAt b i :: decodeLedgerFrom b (i + 1) k

theorem decodeLedgerFrom_succ (b : ByteArray) :
    ∀ (i k : Nat), decodeLedgerFrom b i (k + 1) =
      decodeLedgerFrom b i k ++ [ledgerEntryAt b (i + k)]
  | _, 0 => rfl
  | i, k + 1 => by
    rw [decodeLedgerFrom, decodeLedgerFrom_succ b (i + 1) k, decodeLedgerFrom,
      show i + 1 + k = i + (k + 1) from by omega]
    rfl

/-- The ledger's entries read from the first. -/
theorem decodeLedger_eq_from (b : ByteArray) : ∀ n, decodeLedger b n = decodeLedgerFrom b 0 n
  | 0 => rfl
  | n + 1 => by
    rw [decodeLedger, decodeLedgerFrom_succ, decodeLedger_eq_from b n, Nat.zero_add]
    rfl

theorem length_decodeLedger (b : ByteArray) : ∀ n, (decodeLedger b n).length = n
  | 0 => rfl
  | n + 1 => by rw [decodeLedger, List.length_append, length_decodeLedger b n]; rfl

/-- `b` with `k` zero bytes appended. -/
def growZeros (b : ByteArray) : Nat → ByteArray
  | 0 => b
  | k + 1 => growZeros (b.push 0) k

theorem ByteArray.size_push' (b : ByteArray) (x : UInt8) : (b.push x).size = b.size + 1 := by
  cases b; simp [ByteArray.push, ByteArray.size]

theorem size_growZeros (b : ByteArray) : ∀ k, (growZeros b k).size = b.size + k
  | 0 => rfl
  | k + 1 => by
    rw [growZeros, size_growZeros _ k, ByteArray.size_push']
    omega

theorem get!_growZeros (b : ByteArray) : ∀ (k i : Nat), i < b.size →
    (growZeros b k).get! i = b.get! i
  | 0, _, _ => rfl
  | k + 1, i, h => by
    rw [growZeros, get!_growZeros _ k i (by rw [ByteArray.size_push']; omega)]
    cases b with
    | mk d =>
    simp only [ByteArray.push, ByteArray.get!]
    have h' : i < d.size := h
    rw [getElem!_pos (d.push 0) i (by simp; omega), getElem!_pos d i h', Array.getElem_push]
    simp [h']

/-- A word of `b` below its end reads the same once `b` is grown. -/
theorem le64At_growZeros (b : ByteArray) (k j : Nat) (h : j + 8 ≤ b.size) :
    le64At (growZeros b k) j = le64At b j := by
  simp only [le64At]
  repeat (rw [get!_growZeros b k _ (by omega)])

/-- Entries below `n` are words below byte `24 n`: a buffer that agrees below
that byte decodes the same. -/
theorem decodeLedger_congr (b b' : ByteArray) :
    ∀ n, (∀ j, j + 8 ≤ ledgerEntryBytes * n → le64At b' j = le64At b j) →
      decodeLedger b' n = decodeLedger b n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [decodeLedger, ledgerEntryBytes] at h ⊢
    rw [decodeLedger_congr b b' n (fun j hj => h j (by simp only [ledgerEntryBytes] at hj; omega)),
      h _ (by omega), h _ (by omega), h _ (by omega)]

/-- **WS-ZA ZA5.4: the physical writes a transition owes, as the HAL reads them**
— a buffer of `count` three-word entries (`decodeLedger`), the entry for a write
its `PhysicalWrite.words`.  `ghost` is the list the proofs reason about, and
`encodes` ties the buffer to it, so the list is never built: a write is three
words stored where the buffer lies (`push`), and draining the ledger
(`clear`) keeps the buffer for the next transition. -/
structure PhysicalWriteLedger where
  ghost : SeLe4n.Erased (List PhysicalWrite)
  bytes : ByteArray
  count : Nat
  encodes : decodeLedger bytes count = ghost.out.map PhysicalWrite.words
  room : ledgerEntryBytes * count ≤ bytes.size

namespace PhysicalWriteLedger

/-- The writes the ledger holds, in record order. -/
noncomputable def toList (l : PhysicalWriteLedger) : List PhysicalWrite := l.ghost.out

/-- An empty ledger with room for `ledgerInitialEntries` writes. -/
def empty : PhysicalWriteLedger where
  ghost := SeLe4n.Erased.mk []
  bytes := growZeros ByteArray.empty (ledgerEntryBytes * ledgerInitialEntries)
  count := 0
  encodes := by simp [decodeLedger]
  room := Nat.zero_le _

instance : Inhabited PhysicalWriteLedger := ⟨empty⟩

@[simp] theorem toList_empty : empty.toList = [] := by simp [toList, empty]

/-- The buffer with room for one more entry. -/
@[inline] def roomFor (b : ByteArray) (n : Nat) : ByteArray :=
  if ledgerEntryBytes * n + ledgerEntryBytes ≤ b.size then b
  else growZeros b (ledgerEntryBytes * n + ledgerEntryBytes - b.size)

theorem size_roomFor (b : ByteArray) (n : Nat) :
    ledgerEntryBytes * n + ledgerEntryBytes ≤ (roomFor b n).size := by
  unfold roomFor
  split
  · assumption
  · rw [size_growZeros]; omega

theorem le64At_roomFor (b : ByteArray) (n j : Nat) (h : j + 8 ≤ b.size) :
    le64At (roomFor b n) j = le64At b j := by
  unfold roomFor
  split
  · rfl
  · exact le64At_growZeros b _ j h

/-- The entry `n` of `b` written with `t`, `a`, `v`. -/
@[inline] def writeEntry (b : ByteArray) (n : Nat) (t a v : UInt64) : ByteArray :=
  setLe64 (setLe64 (setLe64 b (ledgerEntryBytes * n) t) (ledgerEntryBytes * n + 8) a)
    (ledgerEntryBytes * n + 16) v

theorem decodeLedger_writeEntry (b : ByteArray) (n : Nat) (t a v : UInt64)
    (hSize : ledgerEntryBytes * n + ledgerEntryBytes ≤ b.size) :
    decodeLedger (writeEntry b n t a v) (n + 1) = decodeLedger b n ++ [(t, a, v)] := by
  simp only [ledgerEntryBytes] at hSize
  simp only [decodeLedger, writeEntry, ledgerEntryBytes]
  have hLow : decodeLedger (writeEntry b n t a v) n = decodeLedger b n := by
    apply decodeLedger_congr
    intro j hj
    simp only [ledgerEntryBytes] at hj
    simp only [writeEntry, ledgerEntryBytes]
    rw [le64At_setLe64_of_disjoint _ _ _ _ (by omega), le64At_setLe64_of_disjoint _ _ _ _ (by omega),
      le64At_setLe64_of_disjoint _ _ _ _ (by omega)]
  simp only [writeEntry, ledgerEntryBytes] at hLow
  rw [hLow]
  simp only [List.append_cancel_left_eq, List.cons.injEq, and_true, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [le64At_setLe64_of_disjoint _ _ _ _ (by omega), le64At_setLe64_of_disjoint _ _ _ _ (by omega),
      le64At_setLe64_same _ _ _ (by omega)]
  · rw [le64At_setLe64_of_disjoint _ _ _ _ (by omega),
      le64At_setLe64_same _ _ _ (by simp only [size_setLe64]; omega)]
  · rw [le64At_setLe64_same _ _ _ (by simp only [size_setLe64]; omega)]

/-- The entries a write is stored after: none when the ledger was `drained`
(its entries handed to the HAL, so the write starts it over), else all of them. -/
@[inline] def baseCount (l : PhysicalWriteLedger) (drained : Bool) : Nat :=
  if drained then 0 else l.count

/-- The writes a write is recorded after: `baseCount`'s entries. -/
noncomputable def baseList (l : PhysicalWriteLedger) (drained : Bool) : List PhysicalWrite :=
  if drained then [] else l.ghost.out

theorem decodeLedger_baseCount (l : PhysicalWriteLedger) (drained : Bool) :
    decodeLedger l.bytes (l.baseCount drained) = (l.baseList drained).map PhysicalWrite.words := by
  unfold baseCount baseList
  split
  · rfl
  · exact l.encodes

theorem room_baseCount (l : PhysicalWriteLedger) (drained : Bool) :
    ledgerEntryBytes * l.baseCount drained ≤ l.bytes.size := by
  unfold baseCount
  split
  · simp
  · exact l.room

/-- **Record one write, as its words**: `t`, `a`, `v` stored as the entry after
`baseCount`, in the buffer where it lies when it has room; the write itself is
ghost.  Out of line, so a caller's `{ st with physicalWrites := … }` hands the
ledger over and the state is written in its cell rather than copied. -/
@[noinline] def pushWords (l : PhysicalWriteLedger) (drained : Bool)
    (w : SeLe4n.Erased PhysicalWrite) (t a v : UInt64) (h : w.out.words = (t, a, v)) :
    PhysicalWriteLedger where
  ghost := SeLe4n.Erased.mk (l.baseList drained ++ [w.out])
  bytes := writeEntry (roomFor l.bytes (l.baseCount drained)) (l.baseCount drained) t a v
  count := l.baseCount drained + 1
  encodes := by
    rw [decodeLedger_writeEntry _ _ _ _ _ (size_roomFor _ _), SeLe4n.Erased.out_mk,
      List.map_append, ← decodeLedger_baseCount, List.map_singleton, h]
    congr 1
    apply decodeLedger_congr
    intro j hj
    apply le64At_roomFor
    have := l.room_baseCount drained
    omega
  room := by
    simp only [writeEntry, size_setLe64]
    have := size_roomFor l.bytes (l.baseCount drained)
    simp only [ledgerEntryBytes] at this ⊢
    omega

/-- **Record one write after `baseCount`'s entries**: its three words, through
`pushWords`, so the write is never built. -/
@[inline] def pushAfter (l : PhysicalWriteLedger) (drained : Bool) (w : PhysicalWrite) :
    PhysicalWriteLedger :=
  pushWords l drained (SeLe4n.Erased.mk w) w.tag w.addr w.value
    (by rw [SeLe4n.Erased.out_mk]; rfl)

/-- **Record one write** after every entry. -/
@[inline] def push (l : PhysicalWriteLedger) (w : PhysicalWrite) : PhysicalWriteLedger :=
  l.pushAfter false w

@[simp] theorem toList_pushAfter (l : PhysicalWriteLedger) (drained : Bool) (w : PhysicalWrite) :
    (l.pushAfter drained w).toList = (if drained then [] else l.toList) ++ [w] := by
  simp only [toList, pushAfter, pushWords, SeLe4n.Erased.out_mk, baseList]

@[simp] theorem toList_push (l : PhysicalWriteLedger) (w : PhysicalWrite) :
    (l.push w).toList = l.toList ++ [w] := by
  simp [push]

/-- **Record writes**, in order. -/
@[inline] def pushAll (l : PhysicalWriteLedger) (ws : List PhysicalWrite) : PhysicalWriteLedger :=
  ws.foldl push l

@[simp] theorem toList_pushAll (l : PhysicalWriteLedger) (ws : List PhysicalWrite) :
    (l.pushAll ws).toList = l.toList ++ ws := by
  induction ws generalizing l with
  | nil => simp [pushAll]
  | cons w ws ih =>
    simp only [pushAll, List.foldl_cons] at ih ⊢
    rw [ih, toList_push, List.append_assoc, List.singleton_append]

/-- **Record writes after `baseCount`'s entries**, in order: the first through
`pushAfter`, the rest after it. -/
@[inline] def pushAllAfter (l : PhysicalWriteLedger) (drained : Bool) :
    List PhysicalWrite → PhysicalWriteLedger
  | [] => l
  | w :: rest => (l.pushAfter drained w).pushAll rest

theorem toList_pushAllAfter_cons (l : PhysicalWriteLedger) (drained : Bool) (w : PhysicalWrite)
    (rest : List PhysicalWrite) :
    (l.pushAllAfter drained (w :: rest)).toList =
      (if drained then [] else l.toList) ++ w :: rest := by
  simp [pushAllAfter]

end PhysicalWriteLedger

end SeLe4n.Kernel.Architecture
