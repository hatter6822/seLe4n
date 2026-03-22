/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# S2-I: Shared Test Helpers

Common test assertion helpers extracted from individual test suites to eliminate
duplication. All test suites should import this module rather than defining
private copies of these functions.
-/

open SeLe4n.Model

namespace SeLe4n.Testing

/-- Boolean assertion with labeled pass/fail output. -/
def expectCond (tag : String) (label : String) (cond : Bool) : IO Unit :=
  if cond then
    IO.println s!"{tag} check passed [{label}]"
  else
    throw <| IO.userError s!"{tag} check failed [{label}]"

/-- Assert that a kernel operation returned an error matching `expected`. -/
def expectError
    (label : String)
    (actual : Except KernelError α)
    (expected : KernelError) : IO Unit :=
  match actual with
  | .ok _ =>
      throw <| IO.userError s!"{label}: expected error {toString expected}, got success"
  | .error err =>
      if err = expected then
        IO.println s!"check passed [{label}]: {toString err}"
      else
        throw <| IO.userError s!"{label}: expected {toString expected}, got {toString err}"

/-- Assert that a kernel operation returned `.ok` with a state. -/
def expectOk
    (label : String)
    (actual : Except KernelError α) : IO α :=
  match actual with
  | .ok value => do
      IO.println s!"check passed [{label}]"
      pure value
  | .error err =>
      throw <| IO.userError s!"{label}: expected success, got {toString err}"

end SeLe4n.Testing
