-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import Lean.Elab.Command
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
-- Both roots, for the reason `ExportCommitDisciplineCensus` records: an
-- `@[export]` in a module only `SeLe4n.lean` imports must be visible here, or
-- this census would pass vacuously about exactly the seams that link.
import SeLe4n
import SeLe4n.Platform.Staged

/-!
# WS-BP BP2.2 — no kernel entry reaches what the kernel's runtime does not provide

The kernel links its own Lean runtime (`rust/sele4n-hal/src/lean_runtime/`).
For a handful of upstream primitives it has no faithful answer, because the
answer comes from an operating system or a C library the kernel does not have:

* **entropy** — `IO.getRandomBytes` answers with zero bytes, since the image has
  no entropy source.  The library initializer seeds `IO.stdGenRef` with it, and
  a failed read there would abort initialization;
* **temporary files** — creating one fails with `unsupportedOperation`;
* **floating-point formatting and `pow`** — each halts the core.

Each of those is sound only if no kernel entry point *uses* the answer.  This
module decides that from the elaborated environment: it walks everything every
production `@[export]` can reach — through definitions' bodies and through
`implemented_by`, which is what compiled code actually calls — and fails the
build if the walk meets `IO.stdGenRef` or any constant implemented by one of
the runtime's environmental or fail-closed symbols.  The seed's value is then
provably dead, and a kernel feature that starts needing randomness, a file, or
a float's text fails here on the day it is written.

The walk descends into **every** constant, core ones included — a core helper
may itself read the generator — and it **over-approximates**: a mention in a
branch never taken counts as reaching.  That is the fail-closed direction for a
claim of absence.  It answers "reaches" when its fuel runs out.

The symbol list is the runtime's own (`io::UNPROVIDED_SEMANTICS` in Rust), and a
Rust test holds the two lists equal, so neither side can grow a primitive the
other does not know about.
-/

namespace SeLe4n.Testing.RuntimeEnvironmentCensus

open Lean Elab Command

/-- The C symbols the kernel's runtime answers environmentally or fail-closed. -/
def runtimeUnprovidedSymbols : List String :=
  ["lean_io_get_random_bytes", "lean_io_create_tempfile", "lean_io_create_tempdir",
   "lean_float_to_string", "lean_float32_to_string", "lean_float_scaleb",
   "lean_float32_scaleb", "pow", "powf"]

/-- The one value the zero-entropy answer flows into. -/
def seededGenerator : Name := `IO.stdGenRef

/-- `true` when `n` is implemented by one of the runtime's unprovided symbols. -/
def isUnprovided (env : Environment) (n : Name) : Bool :=
  match getExternNameFor env `c n with
  | some sym => runtimeUnprovidedSymbols.contains sym
  | none => false

/-- The constants `c`'s compiled code can reach in one step: its body's
constants and, when the compiler substitutes one, its `implemented_by`. -/
def successors (env : Environment) (c : Name) : List Name :=
  let body := match (env.find? c).bind (·.value? (allowOpaque := true)) with
    | some v => v.getUsedConstants.toList
    | none => []
  match Compiler.getImplementedBy? env c with
  | some impl => impl :: body
  | none => body

/-- The first forbidden constant `root` reaches, if any.  An exhausted walk
answers with the root itself, so exhaustion is a failure, never a pass. -/
partial def forbiddenReach (env : Environment) (root : Name) : Option Name :=
  go [root] {} 2000000
where
  go (worklist : List Name) (seen : NameSet) (fuel : Nat) : Option Name :=
    match fuel, worklist with
    | 0, _ => some root
    | _, [] => none
    | fuel' + 1, c :: rest =>
      if c == seededGenerator || isUnprovided env c then some c
      else if seen.contains c then go rest seen fuel'
      else go (successors env c ++ rest) (seen.insert c) fuel'

/-! ## Witnesses

A census whose forbidden set matched nothing would pass whatever the kernel did,
so each direction is planted: a body that reads the generator, one that reaches
a fail-closed float operation only through a helper, one that reaches it only
through `implemented_by`, and one that reaches none. -/

private def censusWitnessReadsGenerator : BaseIO Nat := do
  let g ← IO.stdGenRef.get
  pure (stdNext g).1

private def censusWitnessHelper (x : Float) : String := x.toString

private def censusWitnessIndirectFloat : String := censusWitnessHelper 1.5

private def censusWitnessReference (x : Float) : String := s!"{x.toUInt64}"

@[implemented_by censusWitnessHelper]
private def censusWitnessImplementedBy (x : Float) : String := censusWitnessReference x

private def censusWitnessClean (n : Nat) : Nat := n * 2 + 1

run_cmd Command.liftTermElabM do
  let env ← getEnv
  unless env.header.moduleNames.contains `SeLe4n do
    throwError "runtime-environment census: the production library root `SeLe4n` is not in \
      this environment, so an export defined in a module only it imports would read as absent"
  -- The subjects exist and are what the runtime says they are.
  unless (env.find? seededGenerator).isSome do
    throwError "runtime-environment census: `{seededGenerator}` is not a declaration"
  for sym in runtimeUnprovidedSymbols do
    let carriers := env.constants.toList.filter (fun (n, _) => getExternNameFor env `c n == some sym)
    if carriers.isEmpty then
      throwError "runtime-environment census: no constant is implemented by `{sym}`, so the \
        census would decide nothing about it"
  -- Witnesses, both directions.
  if (forbiddenReach env ``censusWitnessReadsGenerator).isNone then
    throwError "runtime-environment census: a body reading `IO.stdGenRef` is not seen to"
  if (forbiddenReach env ``censusWitnessIndirectFloat).isNone then
    throwError "runtime-environment census: a fail-closed float operation reached through a \
      helper is not seen — the walk is not transitive"
  if (forbiddenReach env ``censusWitnessImplementedBy).isNone then
    throwError "runtime-environment census: a fail-closed operation reached only through \
      `implemented_by` is not seen — the walk reads the reference body, not the compiled one"
  if (forbiddenReach env ``censusWitnessClean).isSome then
    throwError "runtime-environment census: a body reaching none of them is reported as reaching"
  -- The census: every production `@[export]`.
  let exports : List Name := env.constants.toList.filterMap fun (n, _) =>
    if n.components.any (· == `SeLe4n) && (getExportNameFor? env n).isSome then some n else none
  if exports.isEmpty then
    throwError "runtime-environment census: no `@[export]` found — the census would pass \
      vacuously"
  for n in exports do
    if let some bad := forbiddenReach env n then
      throwError "runtime-environment census: the kernel entry `{n}` reaches `{bad}`, which the \
        kernel's runtime answers without an operating system (zero entropy, no file system) or \
        refuses (floating point).  Give the kernel a real provider first, or remove the use."
  logInfo m!"runtime-environment census: {exports.length} kernel `@[export]`s reach neither \
    `IO.stdGenRef` nor any of {runtimeUnprovidedSymbols.length} unprovided runtime symbols"

end SeLe4n.Testing.RuntimeEnvironmentCensus
