-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Kernel.Concurrency.Types

namespace SeLe4n

-- WS-SM SM5.I (per-core register banks): `MachineState` carries one register
-- file *per core* (`Vector RegisterFile numCores`).  `numCores` / `CoreId` /
-- `bootCoreId` come from `Kernel.Concurrency.Types` (a leaf-ish module whose
-- import closure — `Prelude`, `BarrierComposition`, `RobinHood.*` — never
-- reaches `Machine`, so this import introduces no cycle).
open Kernel.Concurrency (numCores CoreId bootCoreId)

/-- Bounded general-purpose register index.
    ARM64: 31 GPRs (x0–x30), plus pc and sp as separate fields.
    Replaces the former `abbrev RegName := Nat` to prevent namespace confusion
    between register indices and other Nat-typed fields. -/
structure RegName where
  val : Nat
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace RegName

/-- Constructor helper for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : RegName := ⟨n⟩

/-- Projection helper for migration ergonomics. -/
@[inline] def toNat (r : RegName) : Nat := r.val

instance : ToString RegName where
  toString r := toString r.toNat

/-- R7-B/L-02: ARM64 GPR count — 31 general-purpose registers (x0–x30) plus
    the zero register (xzr), totaling 32 GPR indices.
    PC and SP are separate `RegisterFile` fields, not GPR indices. -/
def arm64GPRCount : Nat := 32

/-- R7-B/L-02: A register index is valid if it falls within the ARM64 GPR range.
    This predicate is a refinement — `RegName` wraps unbounded `Nat` for proof
    ergonomics, but hardware operations should only use valid indices. -/
def isValid (r : RegName) : Prop := r.val < arm64GPRCount

/-- R7-B/L-02: Decidable validity check for runtime bounds checking. -/
@[inline] def isValidDec (r : RegName) : Bool := r.val < arm64GPRCount

/-- R7-B/L-02: `isValidDec` reflects `isValid`. -/
theorem isValidDec_iff (r : RegName) : r.isValidDec = true ↔ r.isValid := by
  simp [isValidDec, isValid]

/-- Extensionality theorem for RegName. -/
theorem ext {a b : RegName} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

end RegName

/-- Register-width machine word. Carries the raw numeric value from which
    typed kernel references are decoded at syscall boundaries.
    Replaces the former `abbrev RegValue := Nat` to prevent namespace confusion
    between register values and other Nat-typed fields. -/
structure RegValue where
  val : Nat
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace RegValue

/-- Constructor helper for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : RegValue := ⟨n⟩

/-- Projection helper for migration ergonomics. -/
@[inline] def toNat (r : RegValue) : Nat := r.val

/-- R7-C/L-03: A register value is valid if it fits in one machine word. -/
@[inline] def valid (r : RegValue) : Prop := isWord64 r.val

/-- R7-C/L-03: Decidable validity check for runtime use. -/
@[inline] def isValid (r : RegValue) : Bool := isWord64Dec r.val

/-- A register value read from a 64-bit word is valid: `UInt64.toNat` is below
`2^64`. -/
theorem valid_of_uint64 (x : UInt64) : RegValue.valid ⟨x.toNat⟩ :=
  UInt64.toNat_lt_size x

/-- A register value read from a 32-bit word is valid. -/
theorem valid_of_uint32 (x : UInt32) : RegValue.valid ⟨x.toNat⟩ :=
  Nat.lt_trans (UInt32.toNat_lt_size x) (by decide)

instance : ToString RegValue where
  toString r := toString r.toNat

/-- Extensionality theorem for RegValue. -/
theorem ext {a b : RegValue} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

end RegValue

-- ============================================================================
-- LawfulHashable, EquivBEq, LawfulBEq instances for RegName and RegValue
-- ============================================================================

instance : LawfulHashable RegName where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable RegValue where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : EquivBEq RegName := ⟨⟩
instance : EquivBEq RegValue := ⟨⟩

instance : LawfulBEq RegName where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq RegValue where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _

-- ============================================================================
-- Roundtrip and injectivity proofs for RegName and RegValue
-- ============================================================================

/-- RegName roundtrip — construct then project. -/
theorem RegName.toNat_ofNat (n : Nat) : (RegName.ofNat n).toNat = n := rfl
/-- RegName roundtrip — project then reconstruct. -/
theorem RegName.ofNat_toNat (r : RegName) : RegName.ofNat r.toNat = r := rfl
/-- RegName injectivity. -/
theorem RegName.ofNat_injective {n₁ n₂ : Nat} (h : RegName.ofNat n₁ = RegName.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl

/-- RegValue roundtrip — construct then project. -/
theorem RegValue.toNat_ofNat (n : Nat) : (RegValue.ofNat n).toNat = n := rfl
/-- RegValue roundtrip — project then reconstruct. -/
theorem RegValue.ofNat_toNat (r : RegValue) : RegValue.ofNat r.toNat = r := rfl
/-- RegValue injectivity. -/
theorem RegValue.ofNat_injective {n₁ n₂ : Nat} (h : RegValue.ofNat n₁ = RegValue.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl

/-- L-02/WS-E6: Byte-addressed memory store used by the abstract machine model.

**Zero-default semantics:** The default `Memory` function returns `0 : UInt8` for
all addresses (`fun _ => 0`). This models zero-initialized physical memory at boot
time — a common hardware convention and an explicit seL4 kernel assumption for
zeroed untyped memory regions.

**No page-fault model:** Memory access is total (every address returns a byte).
The model does not distinguish mapped from unmapped pages; access control is
enforced at the VSpace adapter layer (`vspaceLookup` returns `translationFault`
for unmapped virtual addresses). Future work may add a partial-memory model
behind the existing `RuntimeBoundaryContract.memoryAccessAllowed` predicate.

**Migration path:** When/if the model introduces partial memory or page-table
effects, the `Memory` type will change to `PAddr → Option UInt8` or an
equivalent, and adapter bridges will convert between the new and old interfaces.
The `RuntimeBoundaryContract.memoryAccessAllowed` predicate already provides
the extension point for this transition. -/
abbrev Memory := PAddr → UInt8

-- ============================================================================
-- AG3-B: MemoryKind and MemoryRegion (moved before MachineState for field use)
-- ============================================================================

/-- H3-prep: Classification of physical memory region kinds.

Used by platform bindings to declare the hardware memory map. Kernel-level
proofs remain total over `Memory = PAddr → UInt8`; the `MemoryKind` annotation
enables platform-specific access checks and MMU permission assignments. -/
inductive MemoryKind where
  | ram
  | device
  | reserved
  deriving Repr, DecidableEq

/-- H3-prep: A contiguous physical memory region with a declared kind.

Platforms declare their memory map as a list of `MemoryRegion` entries. The
abstract kernel does not enforce these bounds directly — enforcement happens
at the `RuntimeBoundaryContract.memoryAccessAllowed` predicate. This type
provides the vocabulary for platform bindings to express address constraints
that the contract can reference. -/
structure MemoryRegion where
  base : PAddr
  size : Nat
  kind : MemoryKind
  deriving Repr, DecidableEq

namespace MemoryRegion

/-- The end address (exclusive) of a memory region. -/
@[inline] def endAddr (r : MemoryRegion) : Nat := r.base.toNat + r.size

/-- Check whether a physical address falls within this region. -/
@[inline] def contains (r : MemoryRegion) (addr : PAddr) : Bool :=
  r.base.toNat ≤ addr.toNat && addr.toNat < r.endAddr

/-- Two regions overlap if their address ranges intersect. -/
def overlaps (r₁ r₂ : MemoryRegion) : Bool :=
  r₁.base.toNat < r₂.endAddr && r₂.base.toNat < r₁.endAddr

theorem contains_iff (r : MemoryRegion) (addr : PAddr) :
    r.contains addr = true ↔ r.base.toNat ≤ addr.toNat ∧ addr.toNat < r.endAddr := by
  simp [contains, endAddr]

/-- WS-H11/A-05: A memory region is well-formed when its size is positive and its end
    address does not overflow the physical address space. This is a `Prop` proof
    obligation — callers must provide evidence that the region satisfies both
    conditions. S1-B: Converted from `Bool` runtime check to `Prop` to ensure
    malformed regions cannot be constructed without explicit proof. -/
def wellFormed (r : MemoryRegion) (physAddrWidth : Nat) : Prop :=
  r.size > 0 ∧ r.endAddr ≤ 2 ^ physAddrWidth

/-- Decidable instance for `MemoryRegion.wellFormed`, enabling `decide`/`native_decide`
    and `if`-expressions over the predicate. -/
instance (r : MemoryRegion) (w : Nat) : Decidable (r.wellFormed w) :=
  inferInstanceAs (Decidable (_ ∧ _))

end MemoryRegion

/-- The number of words a thread's context occupies: `x0`–`x30`, `SP_EL0`,
`ELR_EL1`, `SPSR_EL1` and `TPIDR_EL0`, the order of the HAL's trap frame. -/
def Kernel.Architecture.trapFrameWordCount : Nat := 35

/-- The index of `SP_EL0` in the context's word layout. -/
def Kernel.Architecture.trapFrameSpWord : Nat := 31

/-- The index of `ELR_EL1` (the program counter the thread resumes at). -/
def Kernel.Architecture.trapFramePcWord : Nat := 32

/-- The index of `SPSR_EL1` (the processor state the thread resumes with). -/
def Kernel.Architecture.trapFramePstateWord : Nat := 33

/-- The index of `TPIDR_EL0` (the thread pointer the thread resumes with). -/
def Kernel.Architecture.trapFrameTpidrWord : Nat := 34

/-- **A thread's register context**: the thirty-five 64-bit words the HAL saves
on a trap and restores on return, in the trap frame's order — `x0`–`x30`, then
`SP_EL0`, `ELR_EL1`, `SPSR_EL1` and `TPIDR_EL0`.

The registers are machine words, so the file holds exactly what the hardware
holds: no value outside `[0, 2^64)` exists to be narrowed at the boundary, and
the file is a value with lawful decidable equality.  A structure whose fields
are all `UInt64` compiles to one constructor object with no object fields and
`8 · 35` scalar bytes, field `i` at byte offset `8 · i` — the layout the HAL's
trap frame has, so a saved context is the trap frame's words, stored by value.

`x31` names the zero register: `gpr` reads it as `0` and `writeReg` ignores a
write to it.  `default` (every field `0`) is a fresh thread's context and every
core's bank at boot. -/
structure RegisterFile where
  /-- `x0`. -/
  x0 : UInt64 := 0
  /-- `x1`. -/
  x1 : UInt64 := 0
  /-- `x2`. -/
  x2 : UInt64 := 0
  /-- `x3`. -/
  x3 : UInt64 := 0
  /-- `x4`. -/
  x4 : UInt64 := 0
  /-- `x5`. -/
  x5 : UInt64 := 0
  /-- `x6`. -/
  x6 : UInt64 := 0
  /-- `x7`. -/
  x7 : UInt64 := 0
  /-- `x8`. -/
  x8 : UInt64 := 0
  /-- `x9`. -/
  x9 : UInt64 := 0
  /-- `x10`. -/
  x10 : UInt64 := 0
  /-- `x11`. -/
  x11 : UInt64 := 0
  /-- `x12`. -/
  x12 : UInt64 := 0
  /-- `x13`. -/
  x13 : UInt64 := 0
  /-- `x14`. -/
  x14 : UInt64 := 0
  /-- `x15`. -/
  x15 : UInt64 := 0
  /-- `x16`. -/
  x16 : UInt64 := 0
  /-- `x17`. -/
  x17 : UInt64 := 0
  /-- `x18`. -/
  x18 : UInt64 := 0
  /-- `x19`. -/
  x19 : UInt64 := 0
  /-- `x20`. -/
  x20 : UInt64 := 0
  /-- `x21`. -/
  x21 : UInt64 := 0
  /-- `x22`. -/
  x22 : UInt64 := 0
  /-- `x23`. -/
  x23 : UInt64 := 0
  /-- `x24`. -/
  x24 : UInt64 := 0
  /-- `x25`. -/
  x25 : UInt64 := 0
  /-- `x26`. -/
  x26 : UInt64 := 0
  /-- `x27`. -/
  x27 : UInt64 := 0
  /-- `x28`. -/
  x28 : UInt64 := 0
  /-- `x29`. -/
  x29 : UInt64 := 0
  /-- `x30`. -/
  x30 : UInt64 := 0
  /-- `SP_EL0`, the stack pointer (word 31). -/
  sp : UInt64 := 0
  /-- `ELR_EL1`, the program counter the thread resumes at (word 32). -/
  pc : UInt64 := 0
  /-- `SPSR_EL1` at the trap (word 33): the condition flags, the exception level
  and stack selector (`M[3:0]`) and the interrupt masks the thread returns to.  A
  thread preempted between a compare and its branch resumes with the wrong
  condition unless this is saved with the rest of its context.  `0` is `EL0t`
  with every flag clear and every interrupt unmasked — a fresh thread's state. -/
  pstate : UInt64 := 0
  /-- The thread pointer `TPIDR_EL0` (word 34), which EL0 writes and reads with
  no trap.  It is thread state, not core state: a switch that does not save and
  restore it hands one thread's value to the next — a 64-bit storage channel
  between any two threads that share a core.  seL4 carries it as `TLS_BASE`. -/
  tpidr : UInt64 := 0
  deriving DecidableEq, Inhabited

/-- R6-C/R7-B: Number of general-purpose register indices (`x0`–`x30` and the
    zero register).
    ARM64: 32 (x0–x30 plus xzr/zero register). Tied to `RegName.arm64GPRCount`
    for consistency with the hardware register model. -/
def registerFileGPRCount : Nat := RegName.arm64GPRCount


namespace RegisterFile

open Kernel.Architecture (trapFrameWordCount)

/-- Word `b` of the layout, indexed by a byte — the form the compiler lowers to
a jump table (a `match` on `UInt8` literals compiles to `uint8_t` compares the C
compiler folds; one on `Nat` literals to a chain of `lean_nat_dec_eq`).  `0`
past the layout. -/
def wordOfByte (rf : RegisterFile) : UInt8 → UInt64
  | 0 => rf.x0
  | 1 => rf.x1
  | 2 => rf.x2
  | 3 => rf.x3
  | 4 => rf.x4
  | 5 => rf.x5
  | 6 => rf.x6
  | 7 => rf.x7
  | 8 => rf.x8
  | 9 => rf.x9
  | 10 => rf.x10
  | 11 => rf.x11
  | 12 => rf.x12
  | 13 => rf.x13
  | 14 => rf.x14
  | 15 => rf.x15
  | 16 => rf.x16
  | 17 => rf.x17
  | 18 => rf.x18
  | 19 => rf.x19
  | 20 => rf.x20
  | 21 => rf.x21
  | 22 => rf.x22
  | 23 => rf.x23
  | 24 => rf.x24
  | 25 => rf.x25
  | 26 => rf.x26
  | 27 => rf.x27
  | 28 => rf.x28
  | 29 => rf.x29
  | 30 => rf.x30
  | 31 => rf.sp
  | 32 => rf.pc
  | 33 => rf.pstate
  | 34 => rf.tpidr
  | _ => 0

/-- Word `i` of the layout; `0` past it.  One bound test on the `Nat`, then
`wordOfByte` on the index narrowed to a byte (exact below the bound). -/
def word (rf : RegisterFile) (i : Nat) : UInt64 :=
  if i < trapFrameWordCount then rf.wordOfByte i.toUInt8 else 0

/-- A word past the layout reads as `0`. -/
theorem word_of_ge (rf : RegisterFile) (i : Nat) (h : ¬ i < trapFrameWordCount) :
    rf.word i = 0 := by
  simp [word, h]

/-- The register file whose word `i` is `w i`.  Inlined, so a caller's `w` is
applied at each index directly rather than through a closure.

This is the Lean-side layout pin: the constructor is applied *positionally*,
so field `i` is `w i` by construction, and `word_ofWords` (which reads each
field by *name*) proves that declared position `i` is layout word `i`.  A field
reordered or inserted without the same change here and in `wordOfByte` fails
to elaborate. -/
@[inline] def ofWords (w : Nat → UInt64) : RegisterFile :=
  ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10, w 11, w 12, w 13, w 14, w 15, w 16, w 17, w 18, w 19, w 20, w 21, w 22, w 23, w 24, w 25, w 26, w 27, w 28, w 29, w 30, w 31, w 32, w 33, w 34⟩

/-- **Encoding a register file's words and decoding them is the identity.** -/
@[simp] theorem ofWords_word (rf : RegisterFile) : ofWords rf.word = rf := by
  cases rf; rfl

/-- Two word functions that agree on the layout's words build the same file. -/
theorem ofWords_congr (w w' : Nat → UInt64)
    (h : ∀ i, i < trapFrameWordCount → w i = w' i) : ofWords w = ofWords w' := by
  simp only [ofWords]
  congr 1 <;> exact h _ (by decide)

/-- **Decoding then encoding is the identity on the layout's words.** -/
@[simp] theorem word_ofWords (w : Nat → UInt64) :
    ∀ i, i < trapFrameWordCount → (ofWords w).word i = w i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | 31, _ => rfl
  | 32, _ => rfl
  | 33, _ => rfl
  | 34, _ => rfl
  | n + 35, h => absurd h (by unfold trapFrameWordCount; omega)

/-- Two register files with the same words are equal — the layout reads every
field. -/
theorem ext_word {a b : RegisterFile} (h : ∀ i, i < trapFrameWordCount → a.word i = b.word i) :
    a = b := by
  rw [← ofWords_word a, ← ofWords_word b]
  exact ofWords_congr _ _ h

/-- **General-purpose register `r`** as a `RegValue`: `x0`–`x30` for `r.val < 31`;
`x31` — the zero register — and every index past it read as `0`. -/
def gpr (rf : RegisterFile) (r : RegName) : RegValue :=
  if r.val < 31 then ⟨(rf.word r.val).toNat⟩ else ⟨0⟩

/-- A register file from its `pc`, `sp` and a function giving each of the
thirty-one general-purpose registers by index; `pstate` and `tpidr` are `0`. -/
@[inline] def withGprs (pc sp : UInt64) (g : Nat → UInt64) : RegisterFile :=
  { ofWords (fun i => if i < 31 then g i else 0) with pc, sp }

/-- **Two register files are equal when their `pc`, `sp`, general-purpose
registers, `pstate` and `tpidr` agree.**  `x0`–`x30` are recovered from `gpr`,
since a word is determined by its `toNat`. -/
theorem ext {a b : RegisterFile}
    (hpc : a.pc = b.pc) (hsp : a.sp = b.sp) (hgpr : ∀ r, a.gpr r = b.gpr r)
    (hps : a.pstate = b.pstate) (htp : a.tpidr = b.tpidr) :
    a = b := by
  apply ext_word
  intro i hi
  by_cases hg : i < 31
  · have h := hgpr ⟨i⟩
    simp only [gpr, hg, if_true, RegValue.mk.injEq] at h
    exact UInt64.toNat_inj.mp h
  · have : i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 := by
      unfold trapFrameWordCount at hi; omega
    rcases this with rfl | rfl | rfl | rfl
    · exact hsp
    · exact hpc
    · exact hps
    · exact htp

/-- `BEq` is decidable equality's, so it is lawful: `==` on register files is
propositional equality. -/
theorem beq_iff_eq' (a b : RegisterFile) : (a == b) = true ↔ a = b := beq_iff_eq

/-- `==` is reflexive.  Kept for the consumers that still cite it; a corollary of
`LawfulBEq`. -/
theorem beq_self (a : RegisterFile) : (a == a) = true := beq_self_eq_true a

/-- `==` is symmetric (a `LawfulBEq` corollary, kept for its consumers). -/
theorem beq_symm {a b : RegisterFile} (h : (a == b) = true) : (b == a) = true := by
  rw [beq_iff_eq] at h ⊢; exact h.symm

/-- `==` is transitive (a `LawfulBEq` corollary, kept for its consumers). -/
theorem beq_trans {a b c : RegisterFile} (hab : (a == b) = true) (hbc : (b == c) = true) :
    (a == c) = true := by
  rw [beq_iff_eq] at hab hbc ⊢; exact hab.trans hbc

end RegisterFile

/-- `RegisterFile`'s trace form: the program counter and stack pointer, as the
trace harness has always printed it. -/
instance : Repr RegisterFile where
  reprPrec rf _ := s!"RegisterFile(pc={rf.pc.toNat}, sp={rf.sp.toNat})"


-- ============================================================================
-- AG3-G (H3-ARCH-06): System Register Model
-- ============================================================================

/-- AG3-G: ARM64 system register file.
    Models the key system registers used during exception handling and
    MMU configuration. All values are `UInt64` matching 64-bit register width.

    **Exception registers**: Saved/restored on exception entry/return.
    **Configuration registers**: Set during boot, read during page table walks. -/
structure SystemRegisterFile where
  /-- ELR_EL1: Exception Link Register (return address on exception) -/
  elr_el1 : UInt64 := 0
  /-- ESR_EL1: Exception Syndrome Register (exception cause encoding) -/
  esr_el1 : UInt64 := 0
  /-- SPSR_EL1: Saved Program Status Register -/
  spsr_el1 : UInt64 := 0
  /-- FAR_EL1: Fault Address Register -/
  far_el1 : UInt64 := 0
  /-- SCTLR_EL1: System Control Register (MMU enable, caches, alignment) -/
  sctlr_el1 : UInt64 := 0
  /-- TCR_EL1: Translation Control Register (page table granule, address sizes) -/
  tcr_el1 : UInt64 := 0
  /-- TTBR0_EL1: Translation Table Base Register 0 (user-space page table) -/
  ttbr0_el1 : UInt64 := 0
  /-- TTBR1_EL1: Translation Table Base Register 1 (kernel-space page table) -/
  ttbr1_el1 : UInt64 := 0
  /-- MAIR_EL1: Memory Attribute Indirection Register -/
  mair_el1 : UInt64 := 0
  /-- VBAR_EL1: Vector Base Address Register (exception vector table base) -/
  vbar_el1 : UInt64 := 0
  deriving Repr, DecidableEq

instance : Inhabited SystemRegisterFile where
  default := {}

/-- **WS-BP BP7.9: a thread's FP/SIMD context** — `v0`–`v31`, `FPCR`, `FPSR`, as
the HAL hands it over.

Each 128-bit vector register is two doublewords, low first: word `2 · n` is
`v`n`'s bits [63:0] and word `2 · n + 1` its bits [127:64], the order the HAL's
save and load routines store and load them (`fp_context.S`, one `stp qN, qN+1`
per pair); then `FPCR`, then `FPSR` — `fpContextWordCount` words in all.

This is the boundary representation of the context: the HAL moves the whole of
it across the FFI in **one** call each way (`Platform.FFI.ffiFpCapture` in,
`Platform.FFI.ffiFpStageContext` out), where the seam used to issue one call per
word.  A structure whose fields are all `UInt64` compiles to a single
constructor object with no object fields and `8 · 66` scalar bytes, field `i` at
byte offset `8 · i` — the layout `rust/sele4n-hal/src/ffi.rs` reads and writes
(`FP_CONTEXT_SCALAR_BYTES`).  The layout is pinned the same way as
`Architecture.TrapContext`'s: `ofWords` applies the constructor *positionally*
while `word` reads by field *name*, so `word_ofWords` proves declared position
`i` is layout word `i`; the HAL refuses an object of any other allocated size;
and `rust/sele4n-lean-boundary` executes the compiled layout against the
HAL's offsets on the host.

A fresh thread's context is all zeroes (`default`, every word `0`:
`FpContext.default_word`), which is what the lazy switch loads the first time
the thread uses FP/SIMD: the load overwrites every register it names, so nothing
a previous occupant of the core's registers left behind is visible to it. -/
structure FpContext where
  /-- `v0` bits [63:0] (word 0). -/
  v0Lo : UInt64
  /-- `v0` bits [127:64] (word 1). -/
  v0Hi : UInt64
  /-- `v1` bits [63:0] (word 2). -/
  v1Lo : UInt64
  /-- `v1` bits [127:64] (word 3). -/
  v1Hi : UInt64
  /-- `v2` bits [63:0] (word 4). -/
  v2Lo : UInt64
  /-- `v2` bits [127:64] (word 5). -/
  v2Hi : UInt64
  /-- `v3` bits [63:0] (word 6). -/
  v3Lo : UInt64
  /-- `v3` bits [127:64] (word 7). -/
  v3Hi : UInt64
  /-- `v4` bits [63:0] (word 8). -/
  v4Lo : UInt64
  /-- `v4` bits [127:64] (word 9). -/
  v4Hi : UInt64
  /-- `v5` bits [63:0] (word 10). -/
  v5Lo : UInt64
  /-- `v5` bits [127:64] (word 11). -/
  v5Hi : UInt64
  /-- `v6` bits [63:0] (word 12). -/
  v6Lo : UInt64
  /-- `v6` bits [127:64] (word 13). -/
  v6Hi : UInt64
  /-- `v7` bits [63:0] (word 14). -/
  v7Lo : UInt64
  /-- `v7` bits [127:64] (word 15). -/
  v7Hi : UInt64
  /-- `v8` bits [63:0] (word 16). -/
  v8Lo : UInt64
  /-- `v8` bits [127:64] (word 17). -/
  v8Hi : UInt64
  /-- `v9` bits [63:0] (word 18). -/
  v9Lo : UInt64
  /-- `v9` bits [127:64] (word 19). -/
  v9Hi : UInt64
  /-- `v10` bits [63:0] (word 20). -/
  v10Lo : UInt64
  /-- `v10` bits [127:64] (word 21). -/
  v10Hi : UInt64
  /-- `v11` bits [63:0] (word 22). -/
  v11Lo : UInt64
  /-- `v11` bits [127:64] (word 23). -/
  v11Hi : UInt64
  /-- `v12` bits [63:0] (word 24). -/
  v12Lo : UInt64
  /-- `v12` bits [127:64] (word 25). -/
  v12Hi : UInt64
  /-- `v13` bits [63:0] (word 26). -/
  v13Lo : UInt64
  /-- `v13` bits [127:64] (word 27). -/
  v13Hi : UInt64
  /-- `v14` bits [63:0] (word 28). -/
  v14Lo : UInt64
  /-- `v14` bits [127:64] (word 29). -/
  v14Hi : UInt64
  /-- `v15` bits [63:0] (word 30). -/
  v15Lo : UInt64
  /-- `v15` bits [127:64] (word 31). -/
  v15Hi : UInt64
  /-- `v16` bits [63:0] (word 32). -/
  v16Lo : UInt64
  /-- `v16` bits [127:64] (word 33). -/
  v16Hi : UInt64
  /-- `v17` bits [63:0] (word 34). -/
  v17Lo : UInt64
  /-- `v17` bits [127:64] (word 35). -/
  v17Hi : UInt64
  /-- `v18` bits [63:0] (word 36). -/
  v18Lo : UInt64
  /-- `v18` bits [127:64] (word 37). -/
  v18Hi : UInt64
  /-- `v19` bits [63:0] (word 38). -/
  v19Lo : UInt64
  /-- `v19` bits [127:64] (word 39). -/
  v19Hi : UInt64
  /-- `v20` bits [63:0] (word 40). -/
  v20Lo : UInt64
  /-- `v20` bits [127:64] (word 41). -/
  v20Hi : UInt64
  /-- `v21` bits [63:0] (word 42). -/
  v21Lo : UInt64
  /-- `v21` bits [127:64] (word 43). -/
  v21Hi : UInt64
  /-- `v22` bits [63:0] (word 44). -/
  v22Lo : UInt64
  /-- `v22` bits [127:64] (word 45). -/
  v22Hi : UInt64
  /-- `v23` bits [63:0] (word 46). -/
  v23Lo : UInt64
  /-- `v23` bits [127:64] (word 47). -/
  v23Hi : UInt64
  /-- `v24` bits [63:0] (word 48). -/
  v24Lo : UInt64
  /-- `v24` bits [127:64] (word 49). -/
  v24Hi : UInt64
  /-- `v25` bits [63:0] (word 50). -/
  v25Lo : UInt64
  /-- `v25` bits [127:64] (word 51). -/
  v25Hi : UInt64
  /-- `v26` bits [63:0] (word 52). -/
  v26Lo : UInt64
  /-- `v26` bits [127:64] (word 53). -/
  v26Hi : UInt64
  /-- `v27` bits [63:0] (word 54). -/
  v27Lo : UInt64
  /-- `v27` bits [127:64] (word 55). -/
  v27Hi : UInt64
  /-- `v28` bits [63:0] (word 56). -/
  v28Lo : UInt64
  /-- `v28` bits [127:64] (word 57). -/
  v28Hi : UInt64
  /-- `v29` bits [63:0] (word 58). -/
  v29Lo : UInt64
  /-- `v29` bits [127:64] (word 59). -/
  v29Hi : UInt64
  /-- `v30` bits [63:0] (word 60). -/
  v30Lo : UInt64
  /-- `v30` bits [127:64] (word 61). -/
  v30Hi : UInt64
  /-- `v31` bits [63:0] (word 62). -/
  v31Lo : UInt64
  /-- `v31` bits [127:64] (word 63). -/
  v31Hi : UInt64
  /-- `FPCR` (word 64). -/
  fpcr : UInt64
  /-- `FPSR` (word 65). -/
  fpsr : UInt64
  deriving Repr, DecidableEq

/-- **WS-BP BP7.9**: the words an `FpContext` occupies on the wire. -/
def fpContextWordCount : Nat := 66

namespace FpContext

/-- **WS-BP BP7.9**: word `i` of a context, in the wire layout — the 64 vector
doublewords, `FPCR`, `FPSR`, and `0` past them. -/
def word (c : FpContext) : Nat → UInt64
  | 0 => c.v0Lo
  | 1 => c.v0Hi
  | 2 => c.v1Lo
  | 3 => c.v1Hi
  | 4 => c.v2Lo
  | 5 => c.v2Hi
  | 6 => c.v3Lo
  | 7 => c.v3Hi
  | 8 => c.v4Lo
  | 9 => c.v4Hi
  | 10 => c.v5Lo
  | 11 => c.v5Hi
  | 12 => c.v6Lo
  | 13 => c.v6Hi
  | 14 => c.v7Lo
  | 15 => c.v7Hi
  | 16 => c.v8Lo
  | 17 => c.v8Hi
  | 18 => c.v9Lo
  | 19 => c.v9Hi
  | 20 => c.v10Lo
  | 21 => c.v10Hi
  | 22 => c.v11Lo
  | 23 => c.v11Hi
  | 24 => c.v12Lo
  | 25 => c.v12Hi
  | 26 => c.v13Lo
  | 27 => c.v13Hi
  | 28 => c.v14Lo
  | 29 => c.v14Hi
  | 30 => c.v15Lo
  | 31 => c.v15Hi
  | 32 => c.v16Lo
  | 33 => c.v16Hi
  | 34 => c.v17Lo
  | 35 => c.v17Hi
  | 36 => c.v18Lo
  | 37 => c.v18Hi
  | 38 => c.v19Lo
  | 39 => c.v19Hi
  | 40 => c.v20Lo
  | 41 => c.v20Hi
  | 42 => c.v21Lo
  | 43 => c.v21Hi
  | 44 => c.v22Lo
  | 45 => c.v22Hi
  | 46 => c.v23Lo
  | 47 => c.v23Hi
  | 48 => c.v24Lo
  | 49 => c.v24Hi
  | 50 => c.v25Lo
  | 51 => c.v25Hi
  | 52 => c.v26Lo
  | 53 => c.v26Hi
  | 54 => c.v27Lo
  | 55 => c.v27Hi
  | 56 => c.v28Lo
  | 57 => c.v28Hi
  | 58 => c.v29Lo
  | 59 => c.v29Hi
  | 60 => c.v30Lo
  | 61 => c.v30Hi
  | 62 => c.v31Lo
  | 63 => c.v31Hi
  | 64 => c.fpcr
  | 65 => c.fpsr
  | _ => 0

/-- **WS-BP BP7.9**: the context whose word `i` is `w i`.  Inlined, so a
caller's `w` is applied at each index directly rather than through a closure.

The Lean-side layout pin: the constructor is applied *positionally*, so field
`i` of the structure is `w i` by construction, and `word_ofWords` (which reads
each field by *name*) proves that declared position `i` is layout word `i`.  A
field reordered or inserted in `FpContext` without the same change here and in
`word` fails to elaborate. -/
@[inline] def ofWords (w : Nat → UInt64) : FpContext :=
  ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10, w 11, w 12, w 13, w 14, w 15, w 16, w 17, w 18, w 19, w 20, w 21, w 22, w 23, w 24, w 25, w 26, w 27, w 28, w 29, w 30, w 31, w 32, w 33, w 34, w 35, w 36, w 37, w 38, w 39, w 40, w 41, w 42, w 43, w 44, w 45, w 46, w 47, w 48, w 49, w 50, w 51, w 52, w 53, w 54, w 55, w 56, w 57, w 58, w 59, w 60, w 61, w 62, w 63, w 64, w 65⟩

/-- **Encoding a context's words and decoding them is the identity**, so the
save → wire → TCB and TCB → wire → load paths lose nothing. -/
@[simp] theorem ofWords_word (c : FpContext) : ofWords c.word = c := by
  cases c; rfl

/-- Two word functions that agree on the layout's words build the same context. -/
theorem ofWords_congr (w w' : Nat → UInt64)
    (h : ∀ i, i < fpContextWordCount → w i = w' i) : ofWords w = ofWords w' := by
  simp only [ofWords]
  congr 1 <;> exact h _ (by decide)

/-- **Decoding then encoding is the identity on the layout's words** — every
word below `fpContextWordCount` crosses the boundary unchanged. -/
@[simp] theorem word_ofWords (w : Nat → UInt64) :
    ∀ i, i < fpContextWordCount → (ofWords w).word i = w i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | 31, _ => rfl
  | 32, _ => rfl
  | 33, _ => rfl
  | 34, _ => rfl
  | 35, _ => rfl
  | 36, _ => rfl
  | 37, _ => rfl
  | 38, _ => rfl
  | 39, _ => rfl
  | 40, _ => rfl
  | 41, _ => rfl
  | 42, _ => rfl
  | 43, _ => rfl
  | 44, _ => rfl
  | 45, _ => rfl
  | 46, _ => rfl
  | 47, _ => rfl
  | 48, _ => rfl
  | 49, _ => rfl
  | 50, _ => rfl
  | 51, _ => rfl
  | 52, _ => rfl
  | 53, _ => rfl
  | 54, _ => rfl
  | 55, _ => rfl
  | 56, _ => rfl
  | 57, _ => rfl
  | 58, _ => rfl
  | 59, _ => rfl
  | 60, _ => rfl
  | 61, _ => rfl
  | 62, _ => rfl
  | 63, _ => rfl
  | 64, _ => rfl
  | 65, _ => rfl
  | n + 66, h => absurd h (by unfold fpContextWordCount; omega)

/-- A word past the layout reads `0`. -/
theorem word_of_count_le (c : FpContext) (i : Nat) (h : fpContextWordCount ≤ i) :
    c.word i = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 66 := ⟨i - 66, by unfold fpContextWordCount at h; omega⟩
  rfl

end FpContext

/-- A fresh thread's FP/SIMD context: every word `0`. -/
instance : Inhabited FpContext where
  default := FpContext.ofWords fun _ => 0

/-- Every word of the default context is `0` — the context a fresh thread's
first FP/SIMD use loads names no value a previous occupant of the registers
left behind. -/
theorem FpContext.default_word (i : Nat) : (default : FpContext).word i = 0 := by
  by_cases h : i < fpContextWordCount
  · exact FpContext.word_ofWords _ i h
  · exact FpContext.word_of_count_le _ i (Nat.le_of_not_lt h)

/-- Top-level abstract machine state manipulated by kernel transitions.
    AG3-B (P-04): All `MachineConfig` fields are now carried in machine state
    so that kernel transitions can reference platform parameters without
    requiring a separate config parameter. -/
structure MachineState where
  /-- WS-SM SM5.I (per-core register banks): one `RegisterFile` per core,
      indexed by `CoreId`.  Replaces the former single `regs : RegisterFile`.
      The boot core's bank (`coreRegs.get bootCoreId`) is the executing-core /
      single-core view exposed by the `MachineState.regs` accessor below, so all
      existing single-core code (FFI, boot, the trace harness, `setPC`, the
      scheduler's single-core context save/restore) is
      behaviourally unchanged; the per-core scheduler's context save/restore
      (SM5.B/SM5.D) writes the *operated* core's bank via `setRegsOnCore c`,
      which is what makes `contextMatchesCurrentOnCore` a genuine `∀ c`
      invariant under per-core dispatch (each core's bank matches its own
      current thread; a dispatch on core `c₀` touches only `c₀`'s bank). -/
  coreRegs : _root_.Vector RegisterFile numCores
  memory : Memory
  timer : Nat
  /-- X2-D: Physical address width carried in machine state so that kernel
      transitions can enforce platform-specific PA bounds without requiring
      a separate `MachineConfig` parameter.  Default 52 (ARM64 LPA maximum);
      real platforms override at boot (e.g., 44 for BCM2712). -/
  physicalAddressWidth : Nat := 52
  /-- AG3-B: Register width in bits (e.g., 64 for ARM64). -/
  registerWidth : Nat := 64
  /-- AG3-B: Virtual address width in bits (e.g., 48 for ARMv8). -/
  virtualAddressWidth : Nat := 48
  /-- AG3-B: Standard page size in bytes (e.g., 4096). -/
  pageSize : Nat := 4096
  /-- AG3-B: Maximum number of address-space identifiers (e.g., 65536). -/
  maxASID : Nat := 65536
  /-- AG3-B: Platform memory map: declared physical memory regions. -/
  memoryMap : List MemoryRegion := []
  /-- AG3-B: Number of general-purpose registers (ARM64: 32). -/
  registerCount : Nat := 32
  /-- **PR #889 review round 20**: how many PEs the platform actually has,
      carried in machine state so live transitions can enforce it without a
      `MachineConfig` parameter — the same reason `physicalAddressWidth` is
      here.  Set at boot by `applyMachineConfig` from
      `MachineConfig.declaredCoreCount`; defaults to the model width, so the
      affinity refusal that reads it is inert on a full-width machine. -/
  declaredCoreCount : Nat := SeLe4n.Kernel.Concurrency.numCores
  /-- AG3-G: ARM64 system registers (exception, MMU configuration). -/
  systemRegisters : SystemRegisterFile := default
  /-- AG5-G/AJ3-E (L-04): Interrupt state — models PSTATE.I (IRQ mask bit).
      `true` = interrupts enabled (PSTATE.I = 0, IRQ unmasked).
      `false` = interrupts disabled (PSTATE.I = 1, IRQ masked).
      On ARM64, the CPU boots with PSTATE.I = 1 (interrupts disabled).
      Default is `false` to match hardware reset state. The boot sequence
      explicitly enables interrupts after GIC initialization.
      The kernel runs with interrupts disabled throughout; this field models
      the DAIF register state manipulated by `sele4n-hal/src/interrupts.rs`. -/
  interruptsEnabled : Bool := false
  /-- AK3-L (A-M10 / MEDIUM): Audit trail for pending EOI writes.
      Each entry is an INTID that has been acknowledged but for which
      `endOfInterrupt` has not yet been invoked. The proof-layer invariant
      `kernelExit_eoiPending_empty` asserts this set is empty at every
      kernel-exit point — detecting missing EOIs at the model layer before
      they cause GIC lockup on hardware.

      Modeled as a `List Nat` of raw INTID values (to accommodate both
      in-range and out-of-range INTIDs from AK3-C's `AckError.outOfRange`).
      An empty list is the initial and kernel-exit steady state. -/
  eoiPending : List Nat := []
  /-- AN9-B (DEF-A-M06 / DEF-AK3-I): Witness that a `dsb ish; isb`
      bracket was emitted after the most recent TLB invalidation.
      `true` at init (no TLB entries to invalidate yet); set `true` by
      every `adapterFlushTlb*Hw` operation (the hardware-backed flush
      routines whose Rust counterparts in `sele4n-hal/src/tlb.rs` emit
      DSB ISH + ISB after every `tlbi` per ARM ARM D8.11).

      Pre-AN9-B this was implicit (`tlbBarrierComplete = True`), giving
      a vacuous proof that barriers existed.  AN9-B makes it substantive:
      a future refactor that bypasses the HAL wrappers would set this
      `false` and break the substantive `tlbBarrierComplete` predicate.

      The richer `lastTlbBarrierKind` field below carries the precise
      barrier-leaf set emitted; the boolean is the coarse witness that
      most callers can discharge by `rfl`. -/
  tlbBarrierEmitted : Bool := true
  /-- AN9-B (DEF-A-M06): A 4-bit bitmask of barrier-leaves emitted by
      the most recent TLB-invalidating operation.
        bit 0 (`0x01`) — `dsb ish` was emitted
        bit 1 (`0x02`) — `dsb ishst` was emitted
        bit 2 (`0x04`) — `isb` was emitted
        bit 3 (`0x08`) — `dsb osh` was emitted (cross-cluster, AN9-I)
      The post-tlbi bracket required by ARM ARM D8.11 corresponds to
      bits 0+2 (`0x05`).  `lastTlbBarrierKind ≥ 0x05` is the substantive
      witness that the bracket was emitted; the
      `BarrierKind.subsumes`-formulated theorem
      (`tlbBarrierComplete_subsumes_bridge` in `TlbModel.lean`) proves
      this is equivalent to the algebraic subsumption check.

      Stored as a `Nat` rather than a `BarrierKind` reference to avoid
      a circular import between `Machine.lean` and
      `Architecture/BarrierComposition.lean`. -/
  lastTlbBarrierKind : Nat := 0x05
  /-- **WS-BP BP7.9: whose FP/SIMD state each core's registers hold.**
      `some t` on core `c` means `c`'s `v0`–`v31`, `FPCR` and `FPSR` are
      thread `t`'s *live* values and `t`'s `TCB.fpContext` may be stale;
      `none` means the registers belong to nobody the model tracks, and a
      thread's context lives only in its TCB.  The lazy switch sets it when a
      thread first uses FP/SIMD on the core (`Architecture.fpAccessOnCore`) and
      clears it, saving the live values into the owner's TCB, at the first
      entry whose committed state no longer runs the owner there
      (`Architecture.fpReleaseOnCore`).  The trap is lifted exactly while the
      core resumes its owner (`RestoreTarget.user`'s `fpLive`). -/
  fpOwner : _root_.Vector (Option ThreadId) numCores :=
    _root_.Vector.replicate numCores none
  /-- **PR #904 review (`v0.36.41`): the thread whose EL0 context each core's
      registers hold** — the thread the core's last context restore resumed, or
      `none` for a core resuming its idle loop or nothing.  Written by
      `Concurrency.settleResidencyOnCore` at the end of every state-committing
      entry, and read by the trap-frame save.

      It is **not** the scheduler's `current` slot, and the difference is the
      point.  A remote deschedule clears core `c`'s `current` slot while `c`'s
      hardware still runs the thread at EL0; until `c` takes an exception, the
      thread's live registers are on `c` and nowhere in the model.  So the save
      reads this record where the slot is empty (the frame belongs to the
      resident thread, not to nobody), and a thread resident on one core is not
      resumed on another until the first has saved it
      (`Architecture.residentElsewhere`). -/
  resident : _root_.Vector (Option ThreadId) numCores :=
    _root_.Vector.replicate numCores none

instance : Inhabited MachineState where
  default := { coreRegs := _root_.Vector.replicate numCores default, memory := (fun _ => 0), timer := 0 }

-- ============================================================================
-- WS-SM SM5.I — per-core register-bank accessors + store/load algebra
-- ============================================================================

/-- WS-SM SM5.I: core `c`'s register file. -/
@[inline] def MachineState.regsOnCore (ms : MachineState) (c : CoreId) : RegisterFile :=
  ms.coreRegs.get c

/-- WS-SM SM5.I: write core `c`'s register file. -/
@[inline] def MachineState.setRegsOnCore (ms : MachineState) (c : CoreId)
    (v : RegisterFile) : MachineState :=
  { ms with coreRegs := ms.coreRegs.set c.val v c.isLt }

/-- **WS-BP BP7.9**: the thread whose FP/SIMD state core `c`'s registers hold. -/
@[inline] def MachineState.fpOwnerOnCore (ms : MachineState) (c : CoreId) : Option ThreadId :=
  ms.fpOwner.get c

/-- **WS-BP BP7.9**: record `t?` as the owner of core `c`'s FP/SIMD registers. -/
@[inline] def MachineState.setFpOwnerOnCore (ms : MachineState) (c : CoreId)
    (t? : Option ThreadId) : MachineState :=
  { ms with fpOwner := ms.fpOwner.set c.val t? c.isLt }

@[simp] theorem MachineState.fpOwnerOnCore_setFpOwnerOnCore_self (ms : MachineState)
    (c : CoreId) (t? : Option ThreadId) : (ms.setFpOwnerOnCore c t?).fpOwnerOnCore c = t? := by
  simp only [MachineState.fpOwnerOnCore, MachineState.setFpOwnerOnCore]
  exact SeLe4n.PerCoreVector.get_set_eq ms.fpOwner c t?

@[simp] theorem MachineState.fpOwnerOnCore_setFpOwnerOnCore_ne (ms : MachineState)
    (c c' : CoreId) (t? : Option ThreadId) (h : c ≠ c') :
    (ms.setFpOwnerOnCore c t?).fpOwnerOnCore c' = ms.fpOwnerOnCore c' := by
  simp only [MachineState.fpOwnerOnCore, MachineState.setFpOwnerOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne ms.fpOwner c c' t? h

/-- **PR #904 review (`v0.36.41`)**: the thread whose EL0 context core `c`'s
registers hold. -/
@[inline] def MachineState.residentOnCore (ms : MachineState) (c : CoreId) : Option ThreadId :=
  ms.resident.get c

/-- **PR #904 review (`v0.36.41`)**: record `t?` as core `c`'s resident thread. -/
@[inline] def MachineState.setResidentOnCore (ms : MachineState) (c : CoreId)
    (t? : Option ThreadId) : MachineState :=
  { ms with resident := ms.resident.set c.val t? c.isLt }

@[simp] theorem MachineState.residentOnCore_setResidentOnCore_self (ms : MachineState)
    (c : CoreId) (t? : Option ThreadId) :
    (ms.setResidentOnCore c t?).residentOnCore c = t? := by
  simp only [MachineState.residentOnCore, MachineState.setResidentOnCore]
  exact SeLe4n.PerCoreVector.get_set_eq ms.resident c t?

@[simp] theorem MachineState.residentOnCore_setResidentOnCore_ne (ms : MachineState)
    (c c' : CoreId) (t? : Option ThreadId) (h : c ≠ c') :
    (ms.setResidentOnCore c t?).residentOnCore c' = ms.residentOnCore c' := by
  simp only [MachineState.residentOnCore, MachineState.setResidentOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne ms.resident c c' t? h

/-- A residency write touches nothing but the residency table. -/
@[simp] theorem MachineState.setResidentOnCore_coreRegs (ms : MachineState) (c : CoreId)
    (t? : Option ThreadId) : (ms.setResidentOnCore c t?).coreRegs = ms.coreRegs := rfl

@[simp] theorem MachineState.setResidentOnCore_memory (ms : MachineState) (c : CoreId)
    (t? : Option ThreadId) : (ms.setResidentOnCore c t?).memory = ms.memory := rfl

@[simp] theorem MachineState.setResidentOnCore_fpOwner (ms : MachineState) (c : CoreId)
    (t? : Option ThreadId) : (ms.setResidentOnCore c t?).fpOwner = ms.fpOwner := rfl

/-- **WS-BP BP7.9**: some core's registers hold `tid`'s live FP/SIMD values. -/
def MachineState.fpOwnedOnSomeCore (ms : MachineState) (tid : ThreadId) : Bool :=
  SeLe4n.Kernel.Concurrency.allCores.any fun c => ms.fpOwnerOnCore c == some tid

/-- **WS-BP BP7.9**: the owner test is exactly "some core records `tid`". -/
theorem MachineState.fpOwnedOnSomeCore_eq_false_iff (ms : MachineState) (tid : ThreadId) :
    ms.fpOwnedOnSomeCore tid = false ↔ ∀ c, ms.fpOwnerOnCore c ≠ some tid := by
  unfold MachineState.fpOwnedOnSomeCore
  constructor
  · intro h c hc
    have := List.any_eq_false.mp h c (SeLe4n.Kernel.Concurrency.mem_allCores c)
    simp [hc] at this
  · intro h
    exact List.any_eq_false.mpr fun c _ => by simp [h c]

/-- **PR #904 review (`v0.36.41`)**: some core's registers still hold `tid`'s EL0
context — the core resumed it and has not yet saved it back.  The residency
sibling of `fpOwnedOnSomeCore`, and refused by the destroy path for the same
reason: that core's next entry saves those registers into the TCB stored under
`tid`, so a thread retyped under the id would receive them. -/
def MachineState.residentOnSomeCore (ms : MachineState) (tid : ThreadId) : Bool :=
  SeLe4n.Kernel.Concurrency.allCores.any fun c => ms.residentOnCore c == some tid

/-- **PR #904 review (`v0.36.41`)**: the residency test is exactly "some core
records `tid` as resident". -/
theorem MachineState.residentOnSomeCore_eq_false_iff (ms : MachineState) (tid : ThreadId) :
    ms.residentOnSomeCore tid = false ↔ ∀ c, ms.residentOnCore c ≠ some tid := by
  unfold MachineState.residentOnSomeCore
  constructor
  · intro h c hc
    have := List.any_eq_false.mp h c (SeLe4n.Kernel.Concurrency.mem_allCores c)
    simp [hc] at this
  · intro h
    exact List.any_eq_false.mpr fun c _ => by simp [h c]

/-- **WS-BP BP7.9**: an owner write touches nothing but the owner table. -/
@[simp] theorem MachineState.setFpOwnerOnCore_coreRegs (ms : MachineState) (c : CoreId)
    (t? : Option ThreadId) : (ms.setFpOwnerOnCore c t?).coreRegs = ms.coreRegs := rfl

@[simp] theorem MachineState.setFpOwnerOnCore_memory (ms : MachineState) (c : CoreId)
    (t? : Option ThreadId) : (ms.setFpOwnerOnCore c t?).memory = ms.memory := rfl

/-- WS-SM SM5.I: the executing-core / single-core register view — the **boot
core's** bank.  This is the back-compatible accessor every pre-SM5 single-core
code path reads as `ms.regs`; flipping the field to a per-core `Vector` keeps
this view byte-identical (the boot core's bank replaces the former single
field).  Per-core code uses `regsOnCore c` instead. -/
@[inline] def MachineState.regs (ms : MachineState) : RegisterFile :=
  ms.regsOnCore bootCoreId

/-- WS-SM SM5.I: `regs` is the boot core's bank by definition. -/
theorem MachineState.regs_eq_regsOnCore_bootCore (ms : MachineState) :
    ms.regs = ms.regsOnCore bootCoreId := rfl

/-- WS-SM SM5.I (store/load algebra): read-after-write at the same core. -/
@[simp] theorem MachineState.regsOnCore_setRegsOnCore_self (ms : MachineState)
    (c : CoreId) (v : RegisterFile) : (ms.setRegsOnCore c v).regsOnCore c = v := by
  simp only [MachineState.regsOnCore, MachineState.setRegsOnCore]
  exact SeLe4n.PerCoreVector.get_set_eq ms.coreRegs c v

/-- WS-SM SM5.I (store/load algebra): a per-core write frames every other core's
register bank. -/
@[simp] theorem MachineState.regsOnCore_setRegsOnCore_ne (ms : MachineState)
    (c c' : CoreId) (v : RegisterFile) (h : c ≠ c') :
    (ms.setRegsOnCore c v).regsOnCore c' = ms.regsOnCore c' := by
  simp only [MachineState.regsOnCore, MachineState.setRegsOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne ms.coreRegs c c' v h

/-- WS-SM SM5.I: writing the boot-core bank via `setRegsOnCore bootCoreId`
updates the single-core `regs` view. -/
@[simp] theorem MachineState.regs_setRegsOnCore_bootCore (ms : MachineState)
    (v : RegisterFile) : (ms.setRegsOnCore bootCoreId v).regs = v := by
  simp only [MachineState.regs]
  exact MachineState.regsOnCore_setRegsOnCore_self ms bootCoreId v

/-- WS-SM SM5.I: `setRegsOnCore` frames all per-core fields except `coreRegs`
(it touches only the register banks). -/
@[simp] theorem MachineState.setRegsOnCore_memory (ms : MachineState) (c : CoreId)
    (v : RegisterFile) : (ms.setRegsOnCore c v).memory = ms.memory := rfl

@[simp] theorem MachineState.setRegsOnCore_timer (ms : MachineState) (c : CoreId)
    (v : RegisterFile) : (ms.setRegsOnCore c v).timer = ms.timer := rfl

@[simp] theorem MachineState.setRegsOnCore_interruptsEnabled (ms : MachineState) (c : CoreId)
    (v : RegisterFile) : (ms.setRegsOnCore c v).interruptsEnabled = ms.interruptsEnabled := rfl

@[simp] theorem MachineState.setRegsOnCore_systemRegisters (ms : MachineState) (c : CoreId)
    (v : RegisterFile) : (ms.setRegsOnCore c v).systemRegisters = ms.systemRegisters := rfl

def readReg (rf : RegisterFile) (r : RegName) : RegValue :=
  rf.gpr r

/-- `x`n` := v` for `n < 31`, indexed by a byte: a jump to one field update
(in place when the file is unshared).  The identity past `x30`. -/
def RegisterFile.setGprOfByte (rf : RegisterFile) : UInt8 → UInt64 → RegisterFile
  | 0, v => { rf with x0 := v }
  | 1, v => { rf with x1 := v }
  | 2, v => { rf with x2 := v }
  | 3, v => { rf with x3 := v }
  | 4, v => { rf with x4 := v }
  | 5, v => { rf with x5 := v }
  | 6, v => { rf with x6 := v }
  | 7, v => { rf with x7 := v }
  | 8, v => { rf with x8 := v }
  | 9, v => { rf with x9 := v }
  | 10, v => { rf with x10 := v }
  | 11, v => { rf with x11 := v }
  | 12, v => { rf with x12 := v }
  | 13, v => { rf with x13 := v }
  | 14, v => { rf with x14 := v }
  | 15, v => { rf with x15 := v }
  | 16, v => { rf with x16 := v }
  | 17, v => { rf with x17 := v }
  | 18, v => { rf with x18 := v }
  | 19, v => { rf with x19 := v }
  | 20, v => { rf with x20 := v }
  | 21, v => { rf with x21 := v }
  | 22, v => { rf with x22 := v }
  | 23, v => { rf with x23 := v }
  | 24, v => { rf with x24 := v }
  | 25, v => { rf with x25 := v }
  | 26, v => { rf with x26 := v }
  | 27, v => { rf with x27 := v }
  | 28, v => { rf with x28 := v }
  | 29, v => { rf with x29 := v }
  | 30, v => { rf with x30 := v }
  | _, _ => rf

/-- **Write general-purpose register `r`.**  `x0`–`x30` take `v`; a write to
`x31` — the zero register — or past it changes nothing. -/
def writeReg (rf : RegisterFile) (r : RegName) (v : UInt64) : RegisterFile :=
  if r.val < 31 then rf.setGprOfByte r.val.toUInt8 v else rf

/-- **`writeReg` word by word**: the written register's word is `v`, every other
word is unchanged. -/
theorem writeReg_eq_ofWords (rf : RegisterFile) (r : RegName) (v : UInt64) :
    writeReg rf r v =
      RegisterFile.ofWords (fun i => if i = r.val ∧ r.val < 31 then v else rf.word i) := by
  obtain ⟨n⟩ := r
  unfold writeReg
  dsimp only
  by_cases h : n < 31
  · simp only [h, if_true]
    match n, h with
    | 0, _ => cases rf; rfl
    | 1, _ => cases rf; rfl
    | 2, _ => cases rf; rfl
    | 3, _ => cases rf; rfl
    | 4, _ => cases rf; rfl
    | 5, _ => cases rf; rfl
    | 6, _ => cases rf; rfl
    | 7, _ => cases rf; rfl
    | 8, _ => cases rf; rfl
    | 9, _ => cases rf; rfl
    | 10, _ => cases rf; rfl
    | 11, _ => cases rf; rfl
    | 12, _ => cases rf; rfl
    | 13, _ => cases rf; rfl
    | 14, _ => cases rf; rfl
    | 15, _ => cases rf; rfl
    | 16, _ => cases rf; rfl
    | 17, _ => cases rf; rfl
    | 18, _ => cases rf; rfl
    | 19, _ => cases rf; rfl
    | 20, _ => cases rf; rfl
    | 21, _ => cases rf; rfl
    | 22, _ => cases rf; rfl
    | 23, _ => cases rf; rfl
    | 24, _ => cases rf; rfl
    | 25, _ => cases rf; rfl
    | 26, _ => cases rf; rfl
    | 27, _ => cases rf; rfl
    | 28, _ => cases rf; rfl
    | 29, _ => cases rf; rfl
    | 30, _ => cases rf; rfl
    | n + 31, h => exact absurd h (by omega)
  · simp only [h, if_false, and_false]
    exact (RegisterFile.ofWords_word rf).symm

/-- Word `i` after a register write. -/
theorem word_writeReg (rf : RegisterFile) (r : RegName) (v : UInt64) (i : Nat) :
    (writeReg rf r v).word i = if i = r.val ∧ r.val < 31 then v else rf.word i := by
  rw [writeReg_eq_ofWords]
  by_cases hi : i < Kernel.Architecture.trapFrameWordCount
  · exact RegisterFile.word_ofWords _ i hi
  · have hr : ¬ (i = r.val ∧ r.val < 31) := by
      unfold Kernel.Architecture.trapFrameWordCount at hi; omega
    rw [RegisterFile.word_of_ge _ i hi, if_neg hr, RegisterFile.word_of_ge _ i hi]

/-- A write to the zero register, or past it, changes nothing. -/
theorem writeReg_of_ge (rf : RegisterFile) (r : RegName) (v : UInt64) (h : ¬ r.val < 31) :
    writeReg rf r v = rf := by
  simp [writeReg, h]

def readMem (ms : MachineState) (addr : PAddr) : UInt8 :=
  ms.memory addr

def writeMem (ms : MachineState) (addr : PAddr) (value : UInt8) : MachineState :=
  { ms with memory := fun a => if a = addr then value else ms.memory a }

-- ============================================================================
-- AK7-C (F-M01 / MEDIUM): Bounds-checked memory access helpers
-- ============================================================================

/-- AK7-C (F-M01): An address is in range of the declared memory map when it
    falls within at least one RAM region and its PA fits in the configured
    physical-address width.

    Rationale: `readMem`/`writeMem` are total on `PAddr → UInt8` — they do
    not consult `memoryMap` or `physicalAddressWidth` and therefore cannot
    detect out-of-range accesses. Callers that enforce MMU contracts (kernel
    deployed with a real hardware map) should route through
    `readMemChecked`/`writeMemChecked`, which fail closed with `none` when
    the address is outside the declared RAM window or exceeds the PA width.
    This is a machine-level companion to
    `RuntimeBoundaryContract.memoryAccessAllowed`; the contract adapter
    continues to enforce the full state-level predicate, while these
    helpers capture the sublety at the `MachineState` layer. -/
@[inline] def MachineState.addrInRange (ms : MachineState) (addr : PAddr) : Bool :=
  addr.toNat < 2 ^ ms.physicalAddressWidth &&
  ms.memoryMap.any (fun r => r.kind == .ram && r.contains addr)

/-- AK7-C (F-M01): Bounds-checked memory read. Returns `some byte` when the
    address satisfies `addrInRange`, `none` otherwise. Designed for consumers
    that want fail-closed semantics at the Lean model layer without altering
    the total `readMem` API that drives the existing proof surface. -/
def readMemChecked (ms : MachineState) (addr : PAddr) : Option UInt8 :=
  if ms.addrInRange addr then some (ms.memory addr) else none

/-- AK7-C (F-M01): Bounds-checked memory write. Returns `some ms'` when the
    write is permitted by `addrInRange`, `none` otherwise. -/
def writeMemChecked (ms : MachineState) (addr : PAddr) (value : UInt8) :
    Option MachineState :=
  if ms.addrInRange addr then some (writeMem ms addr value) else none

/-- AK7-C: `readMemChecked` agrees with `readMem` on in-range addresses. -/
theorem readMemChecked_eq_readMem_of_inRange
    (ms : MachineState) (addr : PAddr) (h : ms.addrInRange addr = true) :
    readMemChecked ms addr = some (readMem ms addr) := by
  simp [readMemChecked, readMem, h]

/-- AK7-C: `readMemChecked` returns `none` for out-of-range addresses. -/
theorem readMemChecked_none_of_outRange
    (ms : MachineState) (addr : PAddr) (h : ms.addrInRange addr = false) :
    readMemChecked ms addr = none := by
  simp [readMemChecked, h]

/-- AK7-C: `writeMemChecked` delegates to `writeMem` on in-range addresses. -/
theorem writeMemChecked_eq_writeMem_of_inRange
    (ms : MachineState) (addr : PAddr) (value : UInt8)
    (h : ms.addrInRange addr = true) :
    writeMemChecked ms addr value = some (writeMem ms addr value) := by
  simp [writeMemChecked, h]

/-- AK7-C: `writeMemChecked` returns `none` for out-of-range addresses. -/
theorem writeMemChecked_none_of_outRange
    (ms : MachineState) (addr : PAddr) (value : UInt8)
    (h : ms.addrInRange addr = false) :
    writeMemChecked ms addr value = none := by
  simp [writeMemChecked, h]

/-- AK7-C: A successful `writeMemChecked` preserves all non-memory fields. -/
theorem writeMemChecked_preserves_regs
    (ms ms' : MachineState) (addr : PAddr) (value : UInt8)
    (h : writeMemChecked ms addr value = some ms') :
    ms'.regs = ms.regs := by
  unfold writeMemChecked at h
  split at h
  · cases h; rfl
  · cases h

/-- AK7-C: A successful `writeMemChecked` preserves the timer. -/
theorem writeMemChecked_preserves_timer
    (ms ms' : MachineState) (addr : PAddr) (value : UInt8)
    (h : writeMemChecked ms addr value = some ms') :
    ms'.timer = ms.timer := by
  unfold writeMemChecked at h
  split at h
  · cases h; rfl
  · cases h

def setPC (ms : MachineState) (pc : UInt64) : MachineState :=
  ms.setRegsOnCore bootCoreId { ms.regs with pc }

def tick (ms : MachineState) : MachineState :=
  { ms with timer := ms.timer + 1 }

-- ============================================================================
-- AG5-G: Interrupt state operations
-- ============================================================================

/-- AG5-G: Disable interrupts (set PSTATE.I = 1).
    Models the Rust `disable_interrupts()` from `interrupts.rs`. -/
def disableInterrupts (ms : MachineState) : MachineState :=
  { ms with interruptsEnabled := false }

/-- AG5-G: Enable interrupts (clear PSTATE.I = 0).
    Models the Rust `enable_irq()` from `interrupts.rs`. -/
def enableInterrupts (ms : MachineState) : MachineState :=
  { ms with interruptsEnabled := true }

/-- AG5-G: Execute a function with interrupts disabled, then restore.
    Models the Rust `with_interrupts_disabled()` critical section.
    Saves the original interrupt state, disables interrupts, runs `f`,
    then restores the saved state — matching the DAIF save/restore
    semantics in `interrupts.rs`. -/
def withInterruptsDisabled (f : MachineState → MachineState) (ms : MachineState) :
    MachineState :=
  let saved := ms.interruptsEnabled
  let result := f (disableInterrupts ms)
  { result with interruptsEnabled := saved }

/-- AG5-G: `disableInterrupts` sets interruptsEnabled to false. -/
theorem disableInterrupts_sets_false (ms : MachineState) :
    (disableInterrupts ms).interruptsEnabled = false := rfl

/-- AG5-G: `enableInterrupts` sets interruptsEnabled to true. -/
theorem enableInterrupts_sets_true (ms : MachineState) :
    (enableInterrupts ms).interruptsEnabled = true := rfl

/-- AG5-G: `disableInterrupts` preserves all non-interrupt fields. -/
theorem disableInterrupts_preserves_timer (ms : MachineState) :
    (disableInterrupts ms).timer = ms.timer := rfl

/-- AG5-G: `disableInterrupts` preserves registers. -/
theorem disableInterrupts_preserves_regs (ms : MachineState) :
    (disableInterrupts ms).regs = ms.regs := rfl

/-- AG5-G: `disableInterrupts` preserves memory. -/
theorem disableInterrupts_preserves_memory (ms : MachineState) :
    (disableInterrupts ms).memory = ms.memory := rfl

/-- AG5-G: `enableInterrupts` preserves timer. -/
theorem enableInterrupts_preserves_timer (ms : MachineState) :
    (enableInterrupts ms).timer = ms.timer := rfl

/-- AG5-G: `enableInterrupts` preserves registers. -/
theorem enableInterrupts_preserves_regs (ms : MachineState) :
    (enableInterrupts ms).regs = ms.regs := rfl

/-- AG5-G: `enableInterrupts` preserves memory. -/
theorem enableInterrupts_preserves_memory (ms : MachineState) :
    (enableInterrupts ms).memory = ms.memory := rfl

/-- AG5-G: `withInterruptsDisabled` restores the original interrupt state.
    This matches the Rust `with_interrupts_disabled()` DAIF save/restore. -/
theorem withInterruptsDisabled_restores (f : MachineState → MachineState)
    (ms : MachineState) :
    (withInterruptsDisabled f ms).interruptsEnabled = ms.interruptsEnabled := rfl

/-- AG5-G: `tick` preserves interrupt state. -/
theorem tick_preserves_interruptsEnabled (ms : MachineState) :
    (tick ms).interruptsEnabled = ms.interruptsEnabled := rfl

-- ============================================================================
-- Register read-after-write and frame lemmas (WS-E4 preparation)
-- ============================================================================

theorem readReg_writeReg_eq (rf : RegisterFile) (r : RegName) (v : UInt64) (h : r.val < 31) :
    readReg (writeReg rf r v) r = ⟨v.toNat⟩ := by
  simp [readReg, RegisterFile.gpr, h, word_writeReg]

theorem readReg_writeReg_ne (rf : RegisterFile) (r r' : RegName) (v : UInt64)
    (hNe : r' ≠ r) :
    readReg (writeReg rf r v) r' = readReg rf r' := by
  have hv : r'.val ≠ r.val := fun h => hNe (RegName.ext h)
  simp [readReg, RegisterFile.gpr, word_writeReg, hv]

theorem readMem_writeMem_eq (ms : MachineState) (addr : PAddr) (value : UInt8) :
    readMem (writeMem ms addr value) addr = value := by
  simp [readMem, writeMem]

theorem readMem_writeMem_ne (ms : MachineState) (addr addr' : PAddr) (value : UInt8)
    (hNe : addr' ≠ addr) :
    readMem (writeMem ms addr value) addr' = readMem ms addr' := by
  simp [readMem, writeMem, hNe]

theorem writeReg_preserves_pc (rf : RegisterFile) (r : RegName) (v : UInt64) :
    (writeReg rf r v).pc = rf.pc := by
  have h := word_writeReg rf r v 32
  rw [if_neg (by omega)] at h
  exact h

theorem writeReg_preserves_sp (rf : RegisterFile) (r : RegName) (v : UInt64) :
    (writeReg rf r v).sp = rf.sp := by
  have h := word_writeReg rf r v 31
  rw [if_neg (by omega)] at h
  exact h

theorem writeReg_preserves_pstate (rf : RegisterFile) (r : RegName) (v : UInt64) :
    (writeReg rf r v).pstate = rf.pstate := by
  have h := word_writeReg rf r v 33
  rw [if_neg (by omega)] at h
  exact h

theorem writeReg_preserves_tpidr (rf : RegisterFile) (r : RegName) (v : UInt64) :
    (writeReg rf r v).tpidr = rf.tpidr := by
  have h := word_writeReg rf r v 34
  rw [if_neg (by omega)] at h
  exact h

theorem writeMem_preserves_regs (ms : MachineState) (addr : PAddr) (value : UInt8) :
    (writeMem ms addr value).regs = ms.regs := rfl

theorem writeMem_preserves_timer (ms : MachineState) (addr : PAddr) (value : UInt8) :
    (writeMem ms addr value).timer = ms.timer := rfl

theorem setPC_preserves_memory (ms : MachineState) (pc : UInt64) :
    (setPC ms pc).memory = ms.memory := rfl

theorem setPC_preserves_timer (ms : MachineState) (pc : UInt64) :
    (setPC ms pc).timer = ms.timer := rfl

theorem tick_preserves_regs (ms : MachineState) :
    (tick ms).regs = ms.regs := rfl

theorem tick_preserves_memory (ms : MachineState) :
    (tick ms).memory = ms.memory := rfl

theorem tick_timer_succ (ms : MachineState) :
    (tick ms).timer = ms.timer + 1 := rfl

-- ============================================================================
-- L-02/WS-E6: Default memory zero-initialization proofs
-- ============================================================================

/-- L-02/WS-E6: Default memory returns zero for all addresses.
This formalizes the zero-initialization assumption documented on `Memory`. -/
theorem default_memory_returns_zero (addr : PAddr) :
    (default : MachineState).memory addr = 0 := rfl

/-- L-02/WS-E6: Default register file has PC = 0.
Combined with zero memory, this ensures the boot entry point is deterministic. -/
theorem default_registerFile_pc_zero :
    (default : RegisterFile).pc = 0 := rfl

/-- L-02/WS-E6: Default register file has SP = 0. -/
theorem default_registerFile_sp_zero :
    (default : RegisterFile).sp = 0 := rfl

/-- L-02/WS-E6: Default timer starts at zero. -/
theorem default_timer_zero :
    (default : MachineState).timer = 0 := rfl

-- ============================================================================
-- S6-C: Memory scrubbing primitives (hardware-binding readiness)
-- ============================================================================

/-- S6-C: Zero a contiguous range of physical memory.

    Replaces `memory(addr)` with `0` for all addresses in
    `[base, base + size)`. Addresses outside the range are unchanged.

    This models the hardware operation of zeroing backing memory after
    object deletion. On ARM64, this corresponds to a `DC ZVA` loop or
    `memset(addr, 0, size)` in the kernel's C runtime.

    **Security rationale:** When a kernel object is deleted and its
    backing memory returned to the untyped pool, the memory must be
    zeroed to prevent information leakage between security domains.
    Without scrubbing, a newly allocated object could read data from
    the previous object's memory, violating non-interference. -/
def zeroMemoryRange (ms : MachineState) (base : PAddr) (size : Nat) : MachineState :=
  { ms with memory := fun addr =>
      if base.toNat ≤ addr.toNat ∧ addr.toNat < base.toNat + size
      then 0
      else ms.memory addr }

/-- S6-C: Postcondition predicate — all bytes in `[base, base + size)` are zero. -/
def memoryZeroed (ms : MachineState) (base : PAddr) (size : Nat) : Prop :=
  ∀ (addr : PAddr), base.toNat ≤ addr.toNat → addr.toNat < base.toNat + size →
    ms.memory addr = 0

/-- S6-C: `zeroMemoryRange` establishes the `memoryZeroed` postcondition. -/
theorem zeroMemoryRange_establishes_memoryZeroed
    (ms : MachineState) (base : PAddr) (size : Nat) :
    memoryZeroed (zeroMemoryRange ms base size) base size := by
  intro addr hGe hLt
  simp only [zeroMemoryRange]
  split
  · rfl
  · rename_i h; exact absurd ⟨hGe, hLt⟩ h

/-- S6-C: `zeroMemoryRange` does not modify memory outside the zeroed range. -/
theorem zeroMemoryRange_frame
    (ms : MachineState) (base : PAddr) (size : Nat) (addr : PAddr)
    (hOut : ¬(base.toNat ≤ addr.toNat ∧ addr.toNat < base.toNat + size)) :
    (zeroMemoryRange ms base size).memory addr = ms.memory addr := by
  simp only [zeroMemoryRange]
  split
  · rename_i h; exact absurd h hOut
  · rfl

/-- S6-C: `zeroMemoryRange` preserves register state. -/
theorem zeroMemoryRange_preserves_regs
    (ms : MachineState) (base : PAddr) (size : Nat) :
    (zeroMemoryRange ms base size).regs = ms.regs := rfl

/-- S6-C: `zeroMemoryRange` preserves timer state. -/
theorem zeroMemoryRange_preserves_timer
    (ms : MachineState) (base : PAddr) (size : Nat) :
    (zeroMemoryRange ms base size).timer = ms.timer := rfl

/-- S6-C: Zero-size scrub is a no-op (memory function unchanged). -/
theorem zeroMemoryRange_zero_size_memory
    (ms : MachineState) (base : PAddr) (addr : PAddr) :
    (zeroMemoryRange ms base 0).memory addr = ms.memory addr := by
  simp only [zeroMemoryRange]
  split
  · rename_i h; omega
  · rfl

-- ============================================================================
-- AG3-G: System register read/write operations and frame lemmas
-- ============================================================================

/-- AG3-G: System register index for type-safe read/write operations. -/
inductive SystemRegisterIndex where
  | elr_el1 | esr_el1 | spsr_el1 | far_el1
  | sctlr_el1 | tcr_el1 | ttbr0_el1 | ttbr1_el1 | mair_el1 | vbar_el1
  deriving Repr, DecidableEq

/-- AG3-G: Read a system register by index. -/
def readSystemRegister (ms : MachineState) (idx : SystemRegisterIndex) : UInt64 :=
  match idx with
  | .elr_el1   => ms.systemRegisters.elr_el1
  | .esr_el1   => ms.systemRegisters.esr_el1
  | .spsr_el1  => ms.systemRegisters.spsr_el1
  | .far_el1   => ms.systemRegisters.far_el1
  | .sctlr_el1 => ms.systemRegisters.sctlr_el1
  | .tcr_el1   => ms.systemRegisters.tcr_el1
  | .ttbr0_el1 => ms.systemRegisters.ttbr0_el1
  | .ttbr1_el1 => ms.systemRegisters.ttbr1_el1
  | .mair_el1  => ms.systemRegisters.mair_el1
  | .vbar_el1  => ms.systemRegisters.vbar_el1

/-- AG3-G: Write a system register by index. -/
def writeSystemRegister (ms : MachineState) (idx : SystemRegisterIndex)
    (val : UInt64) : MachineState :=
  let sr := ms.systemRegisters
  let sr' := match idx with
    | .elr_el1   => { sr with elr_el1 := val }
    | .esr_el1   => { sr with esr_el1 := val }
    | .spsr_el1  => { sr with spsr_el1 := val }
    | .far_el1   => { sr with far_el1 := val }
    | .sctlr_el1 => { sr with sctlr_el1 := val }
    | .tcr_el1   => { sr with tcr_el1 := val }
    | .ttbr0_el1 => { sr with ttbr0_el1 := val }
    | .ttbr1_el1 => { sr with ttbr1_el1 := val }
    | .mair_el1  => { sr with mair_el1 := val }
    | .vbar_el1  => { sr with vbar_el1 := val }
  { ms with systemRegisters := sr' }

/-- AG3-G: System register writes don't modify the object store or scheduler.
    Frame lemma (a): preserves objects. Since MachineState doesn't contain
    objects, this is expressed as preserving all non-systemRegisters fields. -/
theorem writeSystemRegister_preserves_regs (ms : MachineState)
    (idx : SystemRegisterIndex) (val : UInt64) :
    (writeSystemRegister ms idx val).regs = ms.regs := by
  cases idx <;> rfl

/-- AG3-G: System register writes don't modify memory. -/
theorem writeSystemRegister_preserves_memory (ms : MachineState)
    (idx : SystemRegisterIndex) (val : UInt64) :
    (writeSystemRegister ms idx val).memory = ms.memory := by
  cases idx <;> rfl

/-- AG3-G: System register writes don't modify the timer. -/
theorem writeSystemRegister_preserves_timer (ms : MachineState)
    (idx : SystemRegisterIndex) (val : UInt64) :
    (writeSystemRegister ms idx val).timer = ms.timer := by
  cases idx <;> rfl

/-- AG3-G: Read-after-write returns the written value. -/
theorem readSystemRegister_writeSystemRegister_eq (ms : MachineState)
    (idx : SystemRegisterIndex) (val : UInt64) :
    readSystemRegister (writeSystemRegister ms idx val) idx = val := by
  cases idx <;> rfl

/-- H3-prep: Platform-declared machine configuration parameters.

Each platform binding provides a `MachineConfig` that declares the hardware's
architectural constants. These are used by platform-specific contracts and
adapters, not by the abstract kernel transitions (which remain `Nat`-based
for proof convenience).

**Register/address widths:** Expressed in bits. The abstract model uses
unbounded `Nat` for all values; widths are advisory constraints that platform
contracts can check against.

**Page size:** Standard memory management unit page size in bytes.

**Max ASID:** Upper bound on the number of address-space identifiers. The
abstract model places no bound; this enables platform contracts to validate
ASID allocation stays within hardware limits. -/
structure MachineConfig where
  /-- Register width in bits (e.g., 64 for ARM64). -/
  registerWidth : Nat
  /-- Virtual address width in bits (e.g., 48 for ARMv8). -/
  virtualAddressWidth : Nat
  /-- Physical address width in bits (e.g., 52 for ARMv8). -/
  physicalAddressWidth : Nat
  /-- Standard page size in bytes (e.g., 4096). -/
  pageSize : Nat
  /-- Maximum number of address-space identifiers (e.g., 65536 for 16-bit ASID). -/
  maxASID : Nat
  /-- Platform memory map: declared physical memory regions. -/
  memoryMap : List MemoryRegion
  /-- WS-J1-C: Number of general-purpose registers in the architecture.
      ARM64: 32 (x0–x30 plus xzr). Used by the register decode layer to
      validate register indices at syscall boundaries. -/
  registerCount : Nat := 32
  /-- **PR #889 review round 20**: how many PEs the platform actually has.

      The model is `numCores` wide, and a binding may declare fewer
      (`PlatformBinding.coreCount`; `SimSingleCorePlatform` declares one).
      WS-RR RR5's `bootAffinitiesDeclared` refuses a *configured* TCB pinned to
      an undeclared core, but `.tcbSetAffinity` accepted any `CoreId` the model
      admits, so a thread could be migrated onto a PE that does not exist —
      queued where nothing runs it — immediately after a successful boot.  The
      count travels with the machine because that is what it describes, and it
      reaches the live state through `applyMachineConfig` like every other
      field here.

      The default is `numCores`, so every existing configuration and fixture
      keeps the full-width model and the affinity refusal below is inert on
      them; only a binding that declares fewer narrows it. -/
  declaredCoreCount : Nat := SeLe4n.Kernel.Concurrency.numCores
  /-- **WS-BP BP3.2**: the physical ranges the kernel keeps for itself — the
      firmware's stub below the image, the image, its stacks, the Lean heap
      arena, and the window the boot places the device tree in.

      The memory map says what the *hardware* has; this says which of that
      RAM the kernel will never hand out.  The boot refuses an untyped that
      overlaps any of it (`Platform.Boot.untypedPlacementRespected`), since an
      untyped over kernel memory lets its holder retype the kernel's own
      pages.  A platform binding supplies it with its bound configuration
      (`PlatformBinding.bindMachineConfig`), because the image's extent is a
      fact about the binding's image — on the RPi5 it is `link.ld`'s
      `KERNEL_RESERVED_END`, held to the Lean constant by
      `scripts/check_link_script.py`.  The default is empty: a configuration
      with no image (the simulation bindings, the trace harness) reserves
      nothing. -/
  kernelReserved : List MemoryRegion := []
  /-- **WS-BP BP7.1**: the pages the boot takes each configured address space's
      top-level translation table from.  A thread's root needs a page of RAM for
      a table walk to start at (`VSpaceRoot.tableBase`); a root carved from an
      untyped is carved *on* one, and a root the boot configures has no untyped
      to be carved from, so the binding reserves a pool inside the kernel's
      reserved extent and the boot requires every configured root to take a
      distinct page of it (`Platform.Boot.bootRootTablesPlaced`).  On the RPi5
      it is `link.ld`'s `.boot_table_pool`, which the HAL zeroes before the
      Lean kernel is entered.  The default is empty: a configuration that
      configures no address space needs none. -/
  bootTablePool : List SeLe4n.PAddr := []
  deriving Repr

/-- AH2-E: Default machine configuration for use as a `PlatformConfig` default.
    These values represent the abstract model's defaults (not any specific
    hardware platform). Platform-specific deployments should always provide
    explicit values via their `PlatformConfig.machineConfig` field.

    Matches existing `MachineState` defaults:
    - `physicalAddressWidth := 52` (ARMv8 max PA width)
    - `registerWidth := 64` (ARM64 default)
    - `virtualAddressWidth := 48` (ARMv8 VA width)
    - `pageSize := 4096` (standard 4K pages)
    - `maxASID := 65536` (16-bit ASID, ARM64)
    - `memoryMap := []` (no regions by default)
    - `registerCount := 32` (ARM64 GPR count) -/
def defaultMachineConfig : MachineConfig where
  registerWidth        := 64
  virtualAddressWidth  := 48
  physicalAddressWidth := 52
  pageSize             := 4096
  maxASID              := 65536
  memoryMap            := []
  registerCount        := 32

/-- R6-C: `registerFileGPRCount` equals `MachineConfig.registerCount`'s default
    value. Ensures the BEq comparison range stays in sync with the architecture. -/
theorem registerFileGPRCount_eq_registerCount_default :
    registerFileGPRCount = 32 := rfl

namespace MachineConfig


/-- A pairwise non-overlap check over the memory map regions.
    S5-J: Complexity is O(n²) where n = memoryMap.length. Acceptable because
    typical platform memory maps have fewer than 20 regions (RPi5 has 5). -/
private def noOverlapAux : List MemoryRegion → Bool
  | [] => true
  | r :: rs => rs.all (fun r' => !r.overlaps r') && noOverlapAux rs

/-- Check whether a natural number is a positive power of two (1, 2, 4, 8, ...).
    Uses bitwise characterization: `n > 0 ∧ n &&& (n - 1) == 0`. -/
@[inline] private def isPowerOfTwo (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1)) == 0


/-- A machine configuration is well-formed when:
    1. All regions have nonzero size.
    2. No two regions overlap.
    3. Page size is a positive power of two.
    4. Register, virtual address, and physical address widths are positive.
    5. WS-H11/A-05: Every region's `endAddr` fits within the physical address space. -/
def wellFormed (cfg : MachineConfig) : Bool :=
  cfg.memoryMap.all (·.size > 0)
  && noOverlapAux cfg.memoryMap
  && isPowerOfTwo cfg.pageSize
  && cfg.registerWidth > 0
  && cfg.virtualAddressWidth > 0
  && cfg.physicalAddressWidth > 0
  && cfg.memoryMap.all (·.endAddr ≤ 2 ^ cfg.physicalAddressWidth)

/-- **WS-BP BP7.10**: `r'` is a non-empty sub-range of `r`. -/
def regionNonEmptyWithin (r' r : MemoryRegion) : Prop :=
  0 < r'.size ∧ r.base.toNat ≤ r'.base.toNat ∧ r'.endAddr ≤ r.endAddr

/-- **WS-BP BP7.10**: `rs'` is `rs` with each region replaced, position by
position, by a non-empty sub-range of itself. -/
def regionsNonEmptyWithin : List MemoryRegion → List MemoryRegion → Prop
  | [], [] => True
  | r' :: rs', r :: rs => regionNonEmptyWithin r' r ∧ regionsNonEmptyWithin rs' rs
  | _, _ => False

/-- Shrinking two regions cannot make them overlap. -/
private theorem not_overlaps_of_within {r r' x x' : MemoryRegion}
    (hr : regionNonEmptyWithin r' r) (hx : regionNonEmptyWithin x' x)
    (h : (!r.overlaps x) = true) : (!r'.overlaps x') = true := by
  unfold regionNonEmptyWithin MemoryRegion.endAddr at hr hx
  simp only [MemoryRegion.overlaps, MemoryRegion.endAddr, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at h ⊢
  omega

private theorem all_not_overlaps_of_within {r r' : MemoryRegion} (hr : regionNonEmptyWithin r' r) :
    ∀ (rs' rs : List MemoryRegion), regionsNonEmptyWithin rs' rs →
      rs.all (fun x => !r.overlaps x) = true → rs'.all (fun x => !r'.overlaps x) = true
  | [], [], _, _ => rfl
  | x' :: rs', x :: rs, hw, h => by
    simp only [regionsNonEmptyWithin] at hw
    simp only [List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨not_overlaps_of_within hr hw.1 h.1, all_not_overlaps_of_within hr rs' rs hw.2 h.2⟩
  | [], _ :: _, hw, _ => hw.elim
  | _ :: _, [], hw, _ => hw.elim

private theorem noOverlapAux_of_within :
    ∀ (rs' rs : List MemoryRegion), regionsNonEmptyWithin rs' rs →
      noOverlapAux rs = true → noOverlapAux rs' = true
  | [], [], _, _ => rfl
  | x' :: rs', x :: rs, hw, h => by
    simp only [regionsNonEmptyWithin] at hw
    simp only [noOverlapAux, Bool.and_eq_true] at h ⊢
    exact ⟨all_not_overlaps_of_within hw.1 rs' rs hw.2 h.1, noOverlapAux_of_within rs' rs hw.2 h.2⟩
  | [], _ :: _, hw, _ => hw.elim
  | _ :: _, [], hw, _ => hw.elim

/-- Every region of `rs'` lies inside its partner in `rs`. -/
private theorem exists_within_of_mem :
    ∀ (rs' rs : List MemoryRegion), regionsNonEmptyWithin rs' rs →
      ∀ r' ∈ rs', ∃ r ∈ rs, regionNonEmptyWithin r' r
  | [], [], _, _, h => nomatch h
  | x' :: rs', x :: rs, hw, r', hr' => by
    simp only [regionsNonEmptyWithin] at hw
    rcases List.mem_cons.mp hr' with rfl | hIn
    · exact ⟨x, List.mem_cons_self .., hw.1⟩
    · obtain ⟨r, hr, h⟩ := exists_within_of_mem rs' rs hw.2 r' hIn
      exact ⟨r, List.mem_cons_of_mem _ hr, h⟩
  | [], _ :: _, hw, _, _ => hw.elim
  | _ :: _, [], hw, _, _ => hw.elim

/-- **WS-BP BP7.10**: a well-formed configuration stays well-formed when each
of its regions is replaced by a non-empty sub-range of itself — positive sizes,
no overlap and the address-width bound are all inherited from the wider
regions.  What lets a platform whose declared RAM is cut short by a board's
own account (the RPi5's first gigabyte, `rpi5MachineConfigForVariant`) reuse
the well-formedness it decides once on the uncut map. -/
theorem wellFormed_of_within (cfg : MachineConfig) (map' : List MemoryRegion)
    (hWithin : regionsNonEmptyWithin map' cfg.memoryMap)
    (hWf : cfg.wellFormed = true) : ({ cfg with memoryMap := map' }).wellFormed = true := by
  unfold wellFormed at hWf ⊢
  simp only [Bool.and_eq_true] at hWf ⊢
  obtain ⟨⟨⟨⟨⟨⟨_, hNo⟩, hPow⟩, hReg⟩, hVa⟩, hPa⟩, hEnd⟩ := hWf
  refine ⟨⟨⟨⟨⟨⟨?_, noOverlapAux_of_within _ _ hWithin hNo⟩, hPow⟩, hReg⟩, hVa⟩, hPa⟩, ?_⟩
  · rw [List.all_eq_true]
    intro r' hr'
    obtain ⟨r, _, hw⟩ := exists_within_of_mem _ _ hWithin r' hr'
    exact decide_eq_true hw.1
  · rw [List.all_eq_true] at hEnd ⊢
    intro r' hr'
    obtain ⟨r, hr, hw⟩ := exists_within_of_mem _ _ hWithin r' hr'
    have := of_decide_eq_true (hEnd r hr)
    exact decide_eq_true (Nat.le_trans hw.2.2 this)

end MachineConfig

-- ============================================================================
-- Syscall register layout — mapping from hardware registers to syscall arguments
-- ============================================================================

/-- Mapping from architecture-specific registers to typed syscall arguments.
    Encodes the real hardware convention for syscall argument passing:
    - capPtrReg: destination capability pointer register (x0 on ARM64)
    - msgInfoReg: message info word register (x1 on ARM64)
    - msgRegs: inline message registers (x2–x5 on ARM64)
    - syscallNumReg: syscall number register (x7 on ARM64) -/
structure SyscallRegisterLayout where
  capPtrReg     : RegName
  msgInfoReg    : RegName
  msgRegs       : Array RegName
  syscallNumReg : RegName
  deriving Repr, DecidableEq

/-- Default ARM64 syscall register layout following the seL4 convention:
    - x0: capability pointer (destination cap address)
    - x1: message info word (length, extra caps, label)
    - x2–x5: inline message registers
    - x7: syscall number -/
def arm64DefaultLayout : SyscallRegisterLayout :=
  { capPtrReg     := ⟨0⟩    -- x0
    msgInfoReg    := ⟨1⟩    -- x1
    msgRegs       := #[⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩]  -- x2–x5
    syscallNumReg := ⟨7⟩ }  -- x7

end SeLe4n
