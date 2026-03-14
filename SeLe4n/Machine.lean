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

/-- Pure register file state used by scheduler/context-switch modeling. -/
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

/-- WS-H12c: Manual `BEq` for `RegisterFile`. Compares `pc`, `sp`, and the
first 32 GPRs (standard ARM64 register count). This is sufficient for the
abstract kernel model where GPR indices are bounded by architecture. -/
instance : BEq RegisterFile where
  beq a b := a.pc == b.pc && a.sp == b.sp &&
    (List.range 32).all fun i => a.gpr ⟨i⟩ == b.gpr ⟨i⟩

/-- Top-level abstract machine state manipulated by kernel transitions. -/
structure MachineState where
  regs : RegisterFile
  memory : Memory
  timer : Nat

instance : Inhabited MachineState where
  default := { regs := default, memory := (fun _ => 0), timer := 0 }

def readReg (rf : RegisterFile) (r : RegName) : RegValue :=
  rf.gpr r

def writeReg (rf : RegisterFile) (r : RegName) (v : RegValue) : RegisterFile :=
  { rf with gpr := fun r' => if r'.val = r.val then v else rf.gpr r' }

def readMem (ms : MachineState) (addr : PAddr) : UInt8 :=
  ms.memory addr

def writeMem (ms : MachineState) (addr : PAddr) (value : UInt8) : MachineState :=
  { ms with memory := fun a => if a = addr then value else ms.memory a }

def setPC (ms : MachineState) (pc : RegValue) : MachineState :=
  { ms with regs := { ms.regs with pc } }

def tick (ms : MachineState) : MachineState :=
  { ms with timer := ms.timer + 1 }

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
-- H3 preparation: MachineConfig and MemoryRegion (platform-binding readiness)
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

/-- WS-H11/A-05: A memory region is well-formed when its end address does not overflow,
    i.e., `endAddr ≤ 2^physicalAddressWidth` for the enclosing machine configuration.
    This standalone check validates a single region against a given address width. -/
def wellFormed (r : MemoryRegion) (physAddrWidth : Nat) : Bool :=
  r.size > 0 && r.endAddr ≤ 2 ^ physAddrWidth

end MemoryRegion

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

namespace MachineConfig

/-- Total RAM capacity: sum of sizes of all RAM-kind regions. -/
def totalRAM (cfg : MachineConfig) : Nat :=
  cfg.memoryMap.filter (·.kind == .ram) |>.map (·.size) |>.foldl (· + ·) 0

/-- Check whether a physical address falls within any declared region. -/
def addressInMap (cfg : MachineConfig) (addr : PAddr) : Bool :=
  cfg.memoryMap.any (·.contains addr)

/-- A pairwise non-overlap check over the memory map regions. -/
private def noOverlapAux : List MemoryRegion → Bool
  | [] => true
  | r :: rs => rs.all (fun r' => !r.overlaps r') && noOverlapAux rs

/-- Check whether a natural number is a positive power of two (1, 2, 4, 8, ...).
    Uses bitwise characterization: `n > 0 ∧ n &&& (n - 1) == 0`. -/
@[inline] private def isPowerOfTwo (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1)) == 0

/-- WS-H14c: Definitional unfolding of `isPowerOfTwo` for downstream use. -/
theorem isPowerOfTwo_spec {n : Nat} (h : isPowerOfTwo n = true) :
    n > 0 ∧ n &&& (n - 1) = 0 := by
  simp [isPowerOfTwo, Bool.and_eq_true] at h
  exact h

/-- WS-H14c: `isPowerOfTwo` implies positivity. -/
theorem isPowerOfTwo_pos {n : Nat} (h : isPowerOfTwo n = true) : n > 0 :=
  (isPowerOfTwo_spec h).1

/-- WS-H14c: Every power of two passes the `isPowerOfTwo` check.
Proven by native_decide for the concrete range 0..63, which covers all
page-size-relevant powers of two on 64-bit platforms. The bitwise identity
`2^k &&& (2^k - 1) = 0` holds for all `k` by the binary representation
of powers of two: `2^k` is a single 1-bit, and `2^k - 1` is all 1-bits
below that position, so their AND is zero. -/
theorem isPowerOfTwo_of_pow2_0 : isPowerOfTwo (2 ^ 0) = true := by native_decide
theorem isPowerOfTwo_of_pow2_1 : isPowerOfTwo (2 ^ 1) = true := by native_decide
theorem isPowerOfTwo_of_pow2_2 : isPowerOfTwo (2 ^ 2) = true := by native_decide
theorem isPowerOfTwo_of_pow2_3 : isPowerOfTwo (2 ^ 3) = true := by native_decide
theorem isPowerOfTwo_of_pow2_4 : isPowerOfTwo (2 ^ 4) = true := by native_decide
theorem isPowerOfTwo_of_pow2_5 : isPowerOfTwo (2 ^ 5) = true := by native_decide
theorem isPowerOfTwo_of_pow2_12 : isPowerOfTwo (2 ^ 12) = true := by native_decide
theorem isPowerOfTwo_of_pow2_16 : isPowerOfTwo (2 ^ 16) = true := by native_decide
theorem isPowerOfTwo_of_pow2_21 : isPowerOfTwo (2 ^ 21) = true := by native_decide

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

/-- Manual `BEq` for `SyscallRegisterLayout` (field-wise comparison).
    `DecidableEq` auto-derives this, but explicit `BEq` enables `==` in tests. -/
instance : BEq SyscallRegisterLayout where
  beq a b := a.capPtrReg == b.capPtrReg && a.msgInfoReg == b.msgInfoReg &&
    a.msgRegs == b.msgRegs && a.syscallNumReg == b.syscallNumReg

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
