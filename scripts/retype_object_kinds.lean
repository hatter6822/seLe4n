-- SPDX-License-Identifier: GPL-3.0-or-later
-- seLe4n  - A Lean Microkernel
-- Copyright (C) 2026  Adam Hall
-- This program comes with ABSOLUTELY NO WARRANTY.
-- This is free software, and you are welcome to redistribute it
-- under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

import SeLe4n.Kernel.Architecture.SyscallArgDecode

/-!
The object kinds an untyped retype can name, as the retype's own decode
(`decodeUntypedRetypeArgs`) reads them: every value of the type word's low byte
the decode accepts, in a message of the retype's full length (`truncationMinimum`), one line each, its tag then the kind it decodes to.  Run by the Tier-4 allocation gate (`scripts/qemu_exerciser_lib.sh`,
`lake env lean --run`), which holds every kind it prints to a carve scenario and
a delete scenario, so the kinds the gate asks about come from the decode and not
from a list kept beside it.
-/

open SeLe4n.Model SeLe4n.Kernel.Architecture.SyscallArgDecode

def main : IO Unit := do
  for n in List.range 256 do
    let decoded : SyscallDecodeResult :=
      { capAddr := SeLe4n.CPtr.ofNat 0,
        msgInfo := { (default : MessageInfo) with length := truncationMinimum .untypedRetype },
        syscallId := .untypedRetype,
        msgRegs := #[⟨n⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] }
    match decodeUntypedRetypeArgs decoded with
    | .ok args => IO.println s!"{n} {repr args.newType}"
    | .error _ => pure ()
