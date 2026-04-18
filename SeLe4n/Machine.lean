/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude

namespace SeLe4n

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

/-- Pure register file state used by scheduler/context-switch modeling.

S4-F: **Design rationale for `gpr : RegName → RegValue` (function representation).**
An `Array RegValue` (size 32) alternative was evaluated and rejected because:

1. **Proof simplicity.** The function representation enables `readReg_writeReg_eq`
   and `readReg_writeReg_ne` to be proved by simple `simp [readReg, writeReg]`.
   Array-based proofs would require bounds checking (`h : i < 32`) threaded
   through every read/write lemma, adding ~50 additional proof obligations.

2. **Extensionality.** `RegisterFile.ext` (pointwise equality) is natural for
   functions. For arrays, extensionality requires `Array.ext_iff` with index
   bounds, complicating preservation proofs across the scheduler and IPC
   subsystems.

3. **BEq instance.** The existing BEq compares all 32 GPR indices in a loop.
   This is semantically equivalent for both representations, but the function
   representation avoids array bounds checks in the BEq implementation.

4. **No performance impact.** The Lean model is not compiled to machine code
   for execution — it exists purely for proof. Register file access in the
   trace harness is infrequent. There is no runtime benefit to array backing.

The function representation will be revisited if/when the model targets
extracted executable code (e.g., via Lean-to-C compilation for the RPi5
bring-up). At that point, a `Fin 32 → RegValue` or `Vector RegValue 32`
representation may be preferable for extraction efficiency. -/
structure RegisterFile where
  pc : RegValue
  sp : RegValue
  gpr : RegName → RegValue

instance : Inhabited RegisterFile where
  default := { pc := ⟨0⟩, sp := ⟨0⟩, gpr := fun _ => ⟨0⟩ }

/-- WS-H12c: Manual `Repr` for `RegisterFile`. Since `gpr` is a function
(`RegName → RegValue`), only `pc` and `sp` are shown in trace output. -/
instance : Repr RegisterFile where
  reprPrec rf _ := s!"RegisterFile(pc={rf.pc.val}, sp={rf.sp.val})"

/-- R6-C/R7-B: Number of GPR indices compared in `RegisterFile` equality.
    ARM64: 32 (x0–x30 plus xzr/zero register). Tied to `RegName.arm64GPRCount`
    for consistency with the hardware register model. -/
def registerFileGPRCount : Nat := RegName.arm64GPRCount

/-- R6-C: Structural `BEq` for `RegisterFile`. Compares `pc`, `sp`, and
all `registerFileGPRCount` GPR indices. Uses a named constant instead of
a magic number to tie the comparison range to the architecture definition.

**S1-J: Lawfulness note.** This `BEq` instance is *not* lawful in the
strict `LawfulBEq` sense (`a == b = true → a = b`) because `gpr` is a
function `RegName → RegValue`. Extensional equality of functions is
undecidable in general; this instance checks equality at all 32 valid
GPR indices (0..31), which is sound for the ARM64 register model since
`RegName.isValid` restricts valid names to this range. For proofs that
require propositional equality of register files, use `RegisterFile.ext`
(which requires pointwise equality of the `gpr` function).

**V7-F: WARNING — non-lawful BEq instance.** Safe for runtime testing and trace
validation. Do NOT use `==` on `RegisterFile` in proof contexts that require
propositional equality — use `RegisterFile.ext` instead. See
`RegisterFile.not_lawfulBEq` for the formal negative witness.

AF2-E: Non-lawful BEq is a known and accepted limitation. ARM64 has
exactly 32 GPRs (x0–x30 + xzr). The `not_lawfulBEq` counterexample
(below) uses index 32 which is unreachable in practice — all kernel
code constructs `RegisterFile` from 32-element arrays. `LawfulBEq`
would require dependent typing (`RegisterFile` over `Fin 32`) which
conflicts with Lean 4 function extensionality for the `gpr` field.
The safety analysis at X5-G (below) confirms this does NOT affect kernel
correctness: `BEq` is used only in test infrastructure and trace
validation, never in proof-critical paths. -/
instance : BEq RegisterFile where
  beq a b := a.pc == b.pc && a.sp == b.sp &&
    (List.range registerFileGPRCount).all fun i => a.gpr ⟨i⟩ == b.gpr ⟨i⟩

/-- AG7-D: BEq reflexivity for RegisterFile. Although the BEq instance is not
    lawful in general (due to the function-typed `gpr` field), `a == a = true`
    holds for any `RegisterFile` because each component comparison (`pc == pc`,
    `sp == sp`, `gpr ⟨i⟩ == gpr ⟨i⟩`) is reflexive via `RegValue`'s lawful BEq. -/
theorem RegisterFile.beq_self (a : RegisterFile) : (a == a) = true := by
  simp [BEq.beq]

/-- U2-N/U-M17: Negative `LawfulBEq` witness for `RegisterFile`.
    `BEq RegisterFile` checks equality at 32 GPR indices but cannot prove
    `a == b = true → a = b` because `gpr` is a function — two extensionally
    different functions may agree on indices 0..31. This instance prevents
    accidental use of `RegisterFile` in proofs that assume `LawfulBEq`. -/
theorem RegisterFile.not_lawfulBEq : ¬ LawfulBEq RegisterFile := by
  intro h
  -- Construct two register files with different gpr functions that agree on 0..31
  -- but differ on an out-of-range index (index 32).
  let f₁ : RegName → RegValue := fun _ => ⟨0⟩
  let f₂ : RegName → RegValue := fun r => if r.val = 32 then ⟨1⟩ else ⟨0⟩
  let r₁ : RegisterFile := { pc := ⟨0⟩, sp := ⟨0⟩, gpr := f₁ }
  let r₂ : RegisterFile := { pc := ⟨0⟩, sp := ⟨0⟩, gpr := f₂ }
  have hBeq : (r₁ == r₂) = true := by decide
  have hPropEq : r₁ = r₂ := @LawfulBEq.eq_of_beq _ _ h r₁ r₂ hBeq
  have hEval : r₁.gpr ⟨32⟩ ≠ r₂.gpr ⟨32⟩ := by decide
  exact hEval (by rw [hPropEq])

-- X5-G (L-2): Safety analysis of RegisterFile's non-lawful BEq.
--
-- The non-lawful BEq does NOT affect kernel correctness because:
-- 1. `RegisterFile.BEq` is used only in `contextMatchesCurrent` comparisons
--    and test infrastructure — never in proof-critical paths.
-- 2. The 32-index check (0..31) covers all ARM64 GPRs (x0–x30 + xzr).
--    Index 32+ is never accessed by kernel code, proven by `regCount = 32`
--    bound in `decodeSyscallArgs` (SyscallArgDecode.lean).
-- 3. The non-lawful edge case (functions agreeing on 0..31 but differing at
--    index ≥ 32) cannot occur in practice because `RegisterFile` is only
--    constructed from finite register arrays with 32 entries. The `gpr`
--    function is always a closure over a finite array, not an arbitrary
--    function on `RegName`.
-- 4. All proofs requiring propositional register-file equality use
--    `RegisterFile.ext` (below), which requires pointwise equality of the
--    `gpr` function — bypassing `BEq` entirely.
--
-- The `not_lawfulBEq` counterexample (above) uses synthetic functions that
-- disagree at out-of-range indices — a scenario impossible in real kernel
-- execution.

/-- S1-J: Extensionality lemma for `RegisterFile`. Two register files are equal
    when their `pc`, `sp`, and `gpr` functions agree. -/
theorem RegisterFile.ext {a b : RegisterFile}
    (hpc : a.pc = b.pc) (hsp : a.sp = b.sp) (hgpr : ∀ r, a.gpr r = b.gpr r) :
    a = b := by
  cases a; cases b; simp at *; exact ⟨hpc, hsp, funext hgpr⟩

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

/-- Top-level abstract machine state manipulated by kernel transitions.
    AG3-B (P-04): All `MachineConfig` fields are now carried in machine state
    so that kernel transitions can reference platform parameters without
    requiring a separate config parameter. -/
structure MachineState where
  regs : RegisterFile
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

instance : Inhabited MachineState where
  default := { regs := default, memory := (fun _ => 0), timer := 0 }

/-- R7-C/L-03: Machine-state word-boundedness invariant.
    Asserts that all register values (PC, SP, and all GPRs) fit in one machine
    word. This is always true on real ARM64 hardware but must be stated as an
    invariant in the abstract model since the underlying `Nat` type is unbounded.

    S1-N: This predicate covers *all* fields in `RegisterFile`: `pc`, `sp`,
    and every valid GPR index (0..31). CPSR/PSTATE is not modeled in the
    abstract register file — ARM64 condition flags are not used by seL4's
    syscall ABI and are therefore outside the kernel's trust boundary.
    If CPSR is added in future hardware-binding work (WS-T), this invariant
    must be extended accordingly. -/
def machineWordBounded (ms : MachineState) : Prop :=
  ms.regs.pc.valid ∧ ms.regs.sp.valid ∧
  ∀ (r : RegName), r.isValid → (ms.regs.gpr r).valid

/-- R7-C/L-03: The default machine state satisfies word-boundedness.
    All registers are initialized to 0, which is trivially word-bounded. -/
theorem machineWordBounded_default : machineWordBounded (default : MachineState) := by
  constructor
  · show (0 : Nat) < 2 ^ 64; omega
  constructor
  · show (0 : Nat) < 2 ^ 64; omega
  · intro _ _; show (0 : Nat) < 2 ^ 64; omega

def readReg (rf : RegisterFile) (r : RegName) : RegValue :=
  rf.gpr r

def writeReg (rf : RegisterFile) (r : RegName) (v : RegValue) : RegisterFile :=
  { rf with gpr := fun r' => if r'.val = r.val then v else rf.gpr r' }

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

def setPC (ms : MachineState) (pc : RegValue) : MachineState :=
  { ms with regs := { ms.regs with pc } }

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

theorem readReg_writeReg_eq (rf : RegisterFile) (r : RegName) (v : RegValue) :
    readReg (writeReg rf r v) r = v := by
  simp [readReg, writeReg]

theorem readReg_writeReg_ne (rf : RegisterFile) (r r' : RegName) (v : RegValue)
    (hNe : r' ≠ r) :
    readReg (writeReg rf r v) r' = readReg rf r' := by
  simp [readReg, writeReg]
  intro h
  exact absurd (RegName.ext h) hNe

theorem readMem_writeMem_eq (ms : MachineState) (addr : PAddr) (value : UInt8) :
    readMem (writeMem ms addr value) addr = value := by
  simp [readMem, writeMem]

theorem readMem_writeMem_ne (ms : MachineState) (addr addr' : PAddr) (value : UInt8)
    (hNe : addr' ≠ addr) :
    readMem (writeMem ms addr value) addr' = readMem ms addr' := by
  simp [readMem, writeMem, hNe]

theorem writeReg_preserves_pc (rf : RegisterFile) (r : RegName) (v : RegValue) :
    (writeReg rf r v).pc = rf.pc := rfl

theorem writeReg_preserves_sp (rf : RegisterFile) (r : RegName) (v : RegValue) :
    (writeReg rf r v).sp = rf.sp := rfl

theorem writeMem_preserves_regs (ms : MachineState) (addr : PAddr) (value : UInt8) :
    (writeMem ms addr value).regs = ms.regs := rfl

theorem writeMem_preserves_timer (ms : MachineState) (addr : PAddr) (value : UInt8) :
    (writeMem ms addr value).timer = ms.timer := rfl

theorem setPC_preserves_memory (ms : MachineState) (pc : RegValue) :
    (setPC ms pc).memory = ms.memory := rfl

theorem setPC_preserves_timer (ms : MachineState) (pc : RegValue) :
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

/-- L-02/WS-E6: Default register file has PC = RegValue 0.
Combined with zero memory, this ensures the boot entry point is deterministic. -/
theorem default_registerFile_pc_zero :
    (default : RegisterFile).pc = ⟨0⟩ := rfl

/-- L-02/WS-E6: Default register file has SP = RegValue 0. -/
theorem default_registerFile_sp_zero :
    (default : RegisterFile).sp = ⟨0⟩ := rfl

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
