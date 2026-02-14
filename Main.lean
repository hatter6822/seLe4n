import SeL4

/-
A minimal executable entrypoint so `lake build` validates module imports and
core definitions compile.
-/
def main : IO Unit :=
  IO.println "seL4 Lean scaffold compiled successfully."
