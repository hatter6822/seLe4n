import SeLe4n

open SeLe4n.Model

/-- Demonstrate a tiny executable path through the kernel model. -/
def bootstrapState : SystemState :=
  { (default : SystemState) with
    objects := fun oid =>
      if oid = 1 then
        some (.tcb {
          tid := 1
          priority := 100
          domain := 0
          cspaceRoot := 10
          vspaceRoot := 20
          ipcBuffer := 4096
        })
      else
        none
    scheduler := { runnable := [1, 2], current := none }
  }

def main : IO Unit := do
  match SeLe4n.Kernel.schedule bootstrapState with
  | .error err => IO.println s!"scheduler error: {reprStr err}"
  | .ok (_, st') =>
      IO.println s!"scheduled thread: {reprStr st'.scheduler.current}"
