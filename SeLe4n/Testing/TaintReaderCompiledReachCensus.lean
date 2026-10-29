/-
seLe4n  - A Lean Microkernel
Copyright (C) 2026  Adam Hall
This program comes with ABSOLUTELY NO WARRANTY.
This is free software, and you are welcome to redistribute it
under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Testing.KernelTransitionReachabilityCensus

/-!
# No compiled path reads the taint map

WS-ZA ZA5.12 deleted the stored taint table: the taint lives in the thread and
notification words, and `SystemState.declassificationTaint` is the reader that
decodes them at one key — the **specification's** view, the value every reader
and propagation theorem is stated over.  The compiled taint step never builds it:
each step captures its sources' words as scalars before the arm and joins words
in place.  This census makes that a build failure rather than a reading.

**The compiled closure.**  From every committing `@[export]`
(`KernelTransitionReachabilityCensus.committingExports`) it follows what the
compiler runs: a constant with a `@[csimp]` replacement or an
`@[implemented_by]` target is followed to that replacement **only**, never into
its own body, because the compiler never runs that body; every other constant is
followed into its value, proofs erased.  `KernelTransitionReachabilityCensus.liveClosure`
follows both edges, which is right for *is this transition wired* and wrong
here: there, the specification body of `dispatchSyscallChecked` reaches the
reader, and it is exactly what the compiler replaces.

**The relation is tested, not the token** — the same walk from the
specification `dispatchSyscallChecked` with its replacement edge ignored
(`specReachesReader`) must reach the reader, so the census is seen to fire on
the path it exists to rule out.
-/

namespace SeLe4n.Testing.TaintReaderCompiledReachCensus

open Lean Elab Command Meta
open SeLe4n.Testing.ExportCommitDisciplineCensus (isProjectConstant)
open SeLe4n.Testing.KernelTransitionReachabilityCensus
  (committingExports isErasedConstant liveClosureFuel)

/-- The reader no compiled path may reach. -/
def taintReader : Name := `SeLe4n.Model.SystemState.declassificationTaint

/-- What the compiler runs in `c`'s place, if anything replaces it. -/
def compiledReplacement (env : Environment) (c : Name) : List Name :=
  ((Lean.Compiler.CSimp.ext.getState env).map.find? c).toList ++
    (Lean.Compiler.getImplementedBy? env c).toList

/-- The compiled closure from `roots`, each reached constant mapped to the one
it was reached from.  With `followReplaced := true` a replaced constant's own
body is followed as well (the specification walk).  `none` on exhausted fuel. -/
partial def compiledClosure (env : Environment) (roots : List Name)
    (followReplaced : Bool := false) (fuel : Nat := liveClosureFuel) :
    Option (NameMap Name) :=
  go (roots.map fun r => (r, r)) {} fuel
where
  go (worklist : List (Name × Name)) (seen : NameMap Name) (fuel : Nat) :
      Option (NameMap Name) :=
    match worklist with
    | [] => some seen
    | (c, parent) :: rest =>
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if seen.contains c || !isProjectConstant c then go rest seen fuel'
      else
        let seen := seen.insert c parent
        if isErasedConstant env c then go rest seen fuel'
        else
          let repl := compiledReplacement env c
          let body : List Name :=
            if !repl.isEmpty && !followReplaced then []
            else match (env.find? c).bind (·.value? (allowOpaque := true)) with
              | none => []
              | some v => v.getUsedConstants.toList
          go ((repl ++ body).map (·, c) ++ rest) seen fuel'

/-- The chain from a root to `n`, root first. -/
partial def pathTo (m : NameMap Name) (n : Name) (acc : List Name := []) : List Name :=
  match m.find? n with
  | some p => if p == n then n :: acc else pathTo m p (n :: acc)
  | none => n :: acc

/-- The witness: the specification dispatcher, walked into its own body, reaches
the reader — so the census below can fire. -/
def specReachesReader (env : Environment) : Bool :=
  match compiledClosure env [`SeLe4n.Kernel.dispatchSyscallChecked] (followReplaced := true) with
  | some m => m.contains taintReader
  | none => true

run_cmd Command.liftTermElabM do
  let env ← getEnv
  unless env.contains taintReader do
    throwError "taint-reader census: `{taintReader}` is not in the environment; the \
      census would pass vacuously."
  unless specReachesReader env do
    throwError "taint-reader census: the specification `dispatchSyscallChecked`, \
      walked into its own body, no longer reaches `{taintReader}` — the witness \
      that this walk can see the reader is gone, so a green result would assert \
      nothing.  Re-derive the witness."
  let roots := committingExports env
  let some m := compiledClosure env roots.toList
    | throwError "taint-reader census: the compiled closure exhausted its fuel of \
        {liveClosureFuel}; an exhausted walk is a refusal, not a pass."
  if m.contains taintReader then
    throwError "taint-reader census failed: compiled code reaches `{taintReader}` \
      through {" → ".intercalate ((pathTo m taintReader).map toString)}.  The \
      compiled taint step reads the words it needs as scalars before the arm; \
      route this path through a fused step (or a `@[csimp]` replacement) instead."
  logInfo s!"taint-reader census: {m.size} constants are compiled-reachable from \
    {roots.size} committing `@[export]`s, none of them `{taintReader}`; the \
    specification dispatcher, walked into its own body, does reach it."

end SeLe4n.Testing.TaintReaderCompiledReachCensus
