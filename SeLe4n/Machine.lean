import SeLe4n.Prelude

namespace SeLe4n

/-- General-purpose register index in the abstract machine model. -/
abbrev RegName := Nat

/-- Register-sized machine word in the abstract machine model. -/
abbrev RegValue := Nat

/-- Byte-addressed memory store used by the abstract machine model.

**L-02/WS-E6: Default memory semantics.** The initial `Memory` function returns
`0 : UInt8` for every physical address. This means all unmapped or uninitialized
memory reads yield zero rather than raising a page fault. This is an intentional
simplification: the model captures deterministic memory-access semantics for
scheduler/IPC reasoning without requiring a page-fault exception model. The
absence of a page-fault model is documented as a known scope boundary—extending
to fault-handling semantics is deferred to future work when VSpace operations
need to model hardware page-table walks.

See `defaultMemory_returns_zero` below for the formal characterization. -/
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

/-- L-02/WS-E6: The default `Memory` returns zero for all physical addresses.
This characterizes the absence of a page-fault model in the abstract machine. -/
theorem defaultMemory_returns_zero (addr : PAddr) :
    (fun (_ : PAddr) => (0 : UInt8)) addr = 0 := rfl

instance : Inhabited MachineState where
  default := { regs := default, memory := fun _ => 0, timer := 0 }

/-- L-02/WS-E6: Default machine state has zero memory at every address. -/
theorem defaultMachineState_memory_zero (addr : PAddr) :
    (default : MachineState).memory addr = 0 := rfl

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
