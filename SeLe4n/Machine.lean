import SeLe4n.Prelude

namespace SeLe4n

/-!
# Machine State Primitives

## L-02/WS-E6: Default memory semantics

The abstract machine model uses a total function `PAddr → UInt8` for memory,
defaulting to `0` for all unmapped addresses. This models a zero-initialized
physical address space — reads from any address always succeed and return a
deterministic value.

**Design choice:** There is intentionally no page-fault model. In the real
seL4 kernel, unmapped virtual addresses trigger a VM fault that is forwarded
to the thread's fault handler. The seLe4n model abstracts this away because:

1. Page faults are an architecture-specific mechanism handled by the VSpace
   subsystem's `vspaceLookup` (which returns `.translationFault` for unmapped
   virtual addresses).
2. Physical memory access is modeled as always-valid at the machine layer,
   with access control enforced by the `RuntimeBoundaryContract.memoryAccessAllowed`
   predicate in the architecture adapter layer.
3. Zero-initialization is a safe default: it does not leak information from
   prior allocations, matching seL4's kernel memory zeroing guarantee.

## F-17/WS-E6: O(n) data structure design rationale (Machine layer)

The `RegisterFile.gpr` field uses a function `RegName → RegValue` rather than
an array or hash map. This yields O(1) reads but O(1) writes that produce
closures (effectively building a chain of `if` tests). For the abstract model's
small register set this is acceptable. See also the F-17 note in `VSpace.lean`
for the analogous `objectIndex` discussion.
-/

/-- General-purpose register index in the abstract machine model. -/
abbrev RegName := Nat

/-- Register-sized machine word in the abstract machine model. -/
abbrev RegValue := Nat

/-- Byte-addressed memory store used by the abstract machine model.
L-02/WS-E6: Total function returning 0 for all unmapped addresses;
no page-fault model (see module docstring). -/
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
