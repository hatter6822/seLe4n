import SeLe4n.Prelude

namespace SeLe4n

/-- General-purpose register index in the abstract machine model. -/
abbrev RegName := Nat

/-- Register-sized machine word in the abstract machine model. -/
abbrev RegValue := Nat

/-- WS-E6/L-02: Byte-addressed memory store used by the abstract machine model.

**Default-memory-returns-zero semantics:** The default `Memory` value is
`fun _ => 0`, meaning every physical address reads as zero until explicitly
written. This is an intentional modeling choice:

1. **No page-fault model.** All addresses are valid and accessible. The real
   seL4 kernel mediates memory access through page tables and raises faults for
   unmapped pages; this model abstracts that away because the formalization
   focuses on kernel-level state transitions, not hardware MMU behavior.

2. **No allocation/deallocation.** Memory is infinite and flat. Physical memory
   partitioning (untyped memory, device regions) is not modeled because the
   formalization scope covers capability and scheduling semantics, not memory
   management internals.

3. **Deterministic reads.** Any address always returns a deterministic value,
   which supports the project's invariant that all transitions are explicit and
   deterministic. Non-deterministic hardware behavior (ECC errors, device
   MMIO) is excluded by the `memoryAccessSafety` architecture assumption
   (see `Architecture/Assumptions.lean`).

Migration path: when physical memory partitioning is modeled, `Memory` should
become `PAddr → Option UInt8` with `none` representing unmapped regions, and
reads of unmapped addresses should produce a `translationFault` error. -/
abbrev Memory := PAddr → UInt8

/-- Pure register file state used by scheduler/context-switch modeling. -/
structure RegisterFile where
  pc : RegValue
  sp : RegValue
  gpr : RegName → RegValue

instance : Inhabited RegisterFile where
  default := { pc := 0, sp := 0, gpr := fun _ => 0 }

/-- Top-level abstract machine state manipulated by kernel transitions. -/
structure MachineState where
  regs : RegisterFile
  memory : Memory
  timer : Nat

/-- WS-E6/L-02: Default machine state. Memory returns zero for all addresses
(see `Memory` documentation above for rationale). Timer starts at 0. -/
instance : Inhabited MachineState where
  default := { regs := default, memory := fun _ => 0, timer := 0 }

def readReg (rf : RegisterFile) (r : RegName) : RegValue :=
  rf.gpr r

def writeReg (rf : RegisterFile) (r : RegName) (v : RegValue) : RegisterFile :=
  { rf with gpr := fun r' => if r' = r then v else rf.gpr r' }

def readMem (ms : MachineState) (addr : PAddr) : UInt8 :=
  ms.memory addr

def writeMem (ms : MachineState) (addr : PAddr) (value : UInt8) : MachineState :=
  { ms with memory := fun a => if a = addr then value else ms.memory a }

def setPC (ms : MachineState) (pc : RegValue) : MachineState :=
  { ms with regs := { ms.regs with pc := pc } }

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
  simp [readReg, writeReg, hNe]

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

end SeLe4n
