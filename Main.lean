import SeLe4

open SeLe4.Model

/-- Demonstrate a tiny executable path through the kernel model. -/
def bootstrapState : SystemState :=
  { (default : SystemState) with
    scheduler := { runnable := [1, 2], current := none }
  }

def main : IO Unit := do
  match SeLe4.Kernel.schedule bootstrapState with
  | .error err => IO.println s!"scheduler error: {reprStr err}"
  | .ok (_, st') =>
      IO.println s!"scheduled thread: {reprStr st'.scheduler.current}"
