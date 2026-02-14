import SeLe4.Prelude

namespace SeLe4

structure RegisterFile where
  pc : Nat
  sp : Nat
  gpr : Nat → Nat

instance : Inhabited RegisterFile where
  default := { pc := 0, sp := 0, gpr := fun _ => 0 }

structure MachineState where
  regs : RegisterFile
  memory : Nat → UInt8
  timer : Nat

instance : Inhabited MachineState where
  default := { regs := default, memory := fun _ => 0, timer := 0 }

end SeLe4
