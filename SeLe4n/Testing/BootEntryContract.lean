-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import Lean.Elab.Command
import SeLe4n.Platform.Staged

/-!
# The hardware boot entry's contract, decided by the elaborator

**PR #889 review round 17.**  SM10.1 writes the declaration carrying
`@[export lean_kernel_main]`: the symbol `rust_boot_main` calls once the Lean
runtime is up.  Two things must be true of it, and nothing in the Lean language
makes them true by construction:

1. it boots through `Platform.FFI.bootAndInitialiseRPi5OrHalt`, so a refused
   boot parks the PE instead of returning to Rust with no kernel state; and
2. no path from it installs kernel state any other way, so the idle threads,
   the deployment labeling and the reserved slots the checked boot establishes
   are the live state's and not merely some state's.

Both were checked, from PR #889 review round 3 onward, by regular expressions
over the Lean source in `scripts/check_kernel_entry_exports.py`.  That was the
wrong tool and the review record says so: eleven rounds of findings against it
were all the same defect in different clothes — a *name* is not the declaration
it spells (`let bootAndInitialiseRPi5 := fun _ => pure (.ok default)`), a
*nested* construct is not a sibling, a *prefix* is not the expression, a
constructor's *head* is not its coverage, a `renaming` binds a name no
declaration mentions.  Every one of those is a question about elaboration, and
the elaborator has already answered it: by the time a declaration is in the
environment its references are resolved constants, its `match` is a matcher
application, and its binders are gone.

So the contract is decided here, over `Environment`.  There is no parsing, and
the questions a parser got wrong cannot be asked: `Expr.getUsedConstants`
returns constants, and a constant has one definition.

The check runs at elaboration time, so building this module *is* the check —
the pattern `SeLe4n.Testing.IpcDethreadingEnvironmentCensus` already uses, and
`scripts/test_tier1_build.sh` builds it on every push.  It is vacuous until the
entry exists (no declaration exports the symbol yet) and decisive after, and
the witnesses at the end keep it from being vacuous *today*: a compliant entry
must be accepted and three token-preserving deviations must each be refused.
-/

namespace SeLe4n.Testing.BootEntryContract

open Lean Elab Command

/-- The symbol the hardware boot entry exports.  `rust_boot_main` declares it
`extern "C"`; `scripts/check_kernel_entry_exports.py` reconciles its absence
from the archive against `EXPECTED_UNRESOLVED` until SM10.1 provides it. -/
def bootEntrySymbol : Name := `lean_kernel_main

/-- The one boot call that entry may make: the checked RPi5 boot with its
failure handled (`Platform.FFI.bootAndInitialiseRPi5OrHalt`).  Naming the
*wrapper* rather than the boot is what removes the error-path question from
this file: the halt is in that definition, once. -/
def approvedBootCall : Name := `SeLe4n.Platform.FFI.bootAndInitialiseRPi5OrHalt

/-- The live kernel state.  A declaration that names one of these outside a
read is an installer, whatever it is called. -/
def kernelStateReferences : List Name :=
  [`SeLe4n.Platform.FFI.kernelStateRef, `SeLe4n.Platform.FFI.kernelLabelingContextRef]

private def stateReferenceSet : Std.HashSet Name :=
  kernelStateReferences.foldl (fun acc n => acc.insert n) {}

/-- Does `e` name a kernel-state reference anywhere that is not the reference
argument of a read?

`ST.Ref.get r` reads `r`; every other position — `set`, `modify`, `modifyGet`,
or the reference passed along as a value — either writes it or hands it to
something this analysis cannot follow, and both count as a write.  That is an
over-approximation in the fail-closed direction: a reader misread as an
installer refuses a boot entry, never admits one. -/
partial def kernelStateWriteInExpr (e : Expr) : Bool :=
  match e with
  | .const n _ => stateReferenceSet.contains n
  | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if let .const head _ := fn then
        if head == ``ST.Ref.get then
          -- The reference itself is read here; anything *computed* to produce
          -- it is still walked.
          args.any fun a =>
            match a.consumeMData with
            | .const _ _ => false
            | a => kernelStateWriteInExpr a
        else
          stateReferenceSet.contains head || args.any kernelStateWriteInExpr
      else
        kernelStateWriteInExpr fn || args.any kernelStateWriteInExpr
  | .lam _ t b _ => kernelStateWriteInExpr t || kernelStateWriteInExpr b
  | .forallE _ t b _ => kernelStateWriteInExpr t || kernelStateWriteInExpr b
  | .letE _ t v b _ =>
      kernelStateWriteInExpr t || kernelStateWriteInExpr v || kernelStateWriteInExpr b
  | .mdata _ b => kernelStateWriteInExpr b
  | .proj _ _ b => kernelStateWriteInExpr b
  | _ => false

/-- The value of `n`, or `none` for a declaration that has none (an `opaque`,
an axiom, a constructor). -/
def declarationValue (env : Environment) (n : Name) : Option Expr :=
  (env.find? n).bind (·.value?)

/-- Does `n`'s own body install kernel state?

The positional walk above is a *tree* walk over an `Expr` that is a DAG with
heavy sharing, so it is run only where it can say anything: `getUsedConstants`
is cached and linear, and a body that never names a reference cannot write one.
On this tree that filter leaves a dozen declarations out of thirty thousand. -/
def declarationWritesKernelState (env : Environment) (n : Name) : Bool :=
  match declarationValue env n with
  | some value =>
      value.getUsedConstants.any stateReferenceSet.contains && kernelStateWriteInExpr value
  | none => false

/-- Does `n` execute?  A theorem's value is a proof, which installs nothing and
whose term is usually far larger than any definition's, so the walk skips them
— the same exclusion the derivation this replaces made. -/
def isExecutableDeclaration (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => false
  | some _ => true
  | none => false

/-- Is `n` this project's?  Only project declarations are walked: a constant
from Lean core or `Std` was compiled before these references existed and
cannot name them.  A declaration with no defining module is one being
elaborated right now — the witnesses below — and is walked, which is the
fail-closed answer. -/
def isProjectDeclaration (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some index =>
      match env.header.moduleNames[index.toNat]? with
      | some name => Name.getRoot name == `SeLe4n
      | none => true
  | none => true

/-- The first declaration reachable from `frontier` that installs kernel state,
not descending into `stop`.

`Expr.getUsedConstants` is what makes this a question about the program rather
than about its text: the entry's references are already resolved, so an alias,
a `renaming`, a local binder of the same name, a qualified or unqualified
spelling are all the same constant here — and a name that resolves to
*something else* is that something else, with no suffix rule to get wrong. -/
partial def unapprovedKernelStateWrite (env : Environment) (stop : Std.HashSet Name) :
    List Name → Std.HashSet Name → Option Name
  | [], _ => none
  | n :: rest, seen =>
      if seen.contains n then
        unapprovedKernelStateWrite env stop rest seen
      else
        let seen := seen.insert n
        if stop.contains n || !isProjectDeclaration env n || !isExecutableDeclaration env n then
          unapprovedKernelStateWrite env stop rest seen
        else if declarationWritesKernelState env n then
          some n
        else
          -- Breadth-first (`rest ++ next`): a write sits a few references below
          -- the boot, and depth-first would descend an instance's elaborated
          -- term first and take a hundred times as long to reach it.
          let next := match declarationValue env n with
            | some value => value.getUsedConstants.toList
            | none => []
          unapprovedKernelStateWrite env stop (rest ++ next) seen

/-- Why `entry` does not meet the boot-entry contract; `[]` when it does. -/
def bootEntryContractViolations (env : Environment) (entry : Name) : List String :=
  let uses := match declarationValue env entry with
    | some value => value.getUsedConstants.toList
    | none => []
  let missing :=
    if uses.contains approvedBootCall then []
    else [s!"`{entry}` does not call `{approvedBootCall}` — the hardware boot entry must \
           boot through the checked platform boot with its failure handled, so a refused \
           boot parks the PE instead of returning to Rust with no kernel state"]
  let bypass :=
    match unapprovedKernelStateWrite env (stateReferenceSet.insert approvedBootCall)
            [entry] {} with
    | some writer =>
        [s!"`{entry}` reaches `{writer}`, which installs kernel state without going through \
            `{approvedBootCall}` — a path around the checked boot leaves the live state \
            without the idle threads, the deployment labeling and the reserved slots it \
            establishes"]
    | none => []
  missing ++ bypass

/-- Every declaration exporting `bootEntrySymbol`.  Read off the environment,
so an `@[inline, export lean_kernel_main]`, an `@[export]` in any namespace and
an entry in any module are all found, and a commented-out one is not there at
all. -/
def bootEntryDeclarations (env : Environment) : List Name :=
  env.constants.toList.foldl
    (fun acc (n, _) => if getExportNameFor? env n == some bootEntrySymbol then n :: acc else acc)
    []

/-! ## Witnesses

The check above is vacuous until SM10.1 writes the entry, and a vacuous check
reads exactly like a passing one.  These four declarations are what a boot
entry could be; the elaboration below requires the analysis to accept the first
and refuse the other three.  Each deviation **keeps** the tokens a text scanner
looks for — the boot call, the halt, the `match`, the `.error` arm — and breaks
the relation, which is the mutation this repository's gates are tested by. -/

/-- The shape SM10.1's entry must have. -/
private def bootEntryWitnessCompliant (config : Platform.Boot.PlatformConfig) : BaseIO Unit :=
  Platform.FFI.bootAndInitialiseRPi5OrHalt config

/-- Keeps the checked boot, the `match`, the `.error` arm and the halt, and
installs the state itself — so a *later* change to what the checked boot
establishes would not reach the live state. -/
private def bootEntryWitnessBypass (config : Platform.Boot.PlatformConfig) : BaseIO Unit := do
  match ← Platform.FFI.bootAndInitialiseRPi5 config with
  | .ok st => Platform.FFI.initialiseKernelState st
  | .error _ => Platform.FFI.ffiFatalHaltAll

/-- Keeps the approved call *and* installs state beside it. -/
private def bootEntryWitnessSideInstall (config : Platform.Boot.PlatformConfig) : BaseIO Unit := do
  Platform.FFI.bootAndInitialiseRPi5OrHalt config
  Platform.FFI.initialiseKernelState default

/-- Installs nothing at all: the image would idle with no kernel. -/
private def bootEntryWitnessUnbooted (_config : Platform.Boot.PlatformConfig) : BaseIO Unit :=
  pure ()

run_cmd do
  let env ← liftCoreM getEnv
  -- The write detector sees a write and does not see a read.
  unless declarationWritesKernelState env `SeLe4n.Platform.FFI.initialiseKernelState do
    throwError "boot-entry contract: the kernel-state write detector does not see \
      `initialiseKernelState`, so every entry would pass"
  if declarationWritesKernelState env `SeLe4n.Platform.FFI.getKernelState then
    throwError "boot-entry contract: the kernel-state write detector reports a read \
      (`getKernelState`) as an installer"
  -- The reach half: a write is reachable from the checked boot when nothing
  -- stops the walk, and is not when the approved wrapper does.
  if (unapprovedKernelStateWrite env stateReferenceSet
        [`SeLe4n.Platform.FFI.bootAndInitialiseRPi5] {}).isNone
  then
    throwError "boot-entry contract: no kernel-state write is reachable from the checked \
      boot, so the reachability half detects nothing"
  -- The witnesses.
  unless (bootEntryContractViolations env ``bootEntryWitnessCompliant).isEmpty do
    throwError "boot-entry contract: the compliant witness was refused: \
      {bootEntryContractViolations env ``bootEntryWitnessCompliant}"
  for witness in [``bootEntryWitnessBypass, ``bootEntryWitnessSideInstall,
                  ``bootEntryWitnessUnbooted] do
    if (bootEntryContractViolations env witness).isEmpty then
      throwError "boot-entry contract: the deviating witness `{witness}` was accepted"
  -- The contract itself.
  match bootEntryDeclarations env with
  | [] =>
      logInfo m!"boot-entry contract: no declaration exports `{bootEntrySymbol}` yet \
        (SM10.1 writes it); the analysis is pinned by its four witnesses"
  | [entry] =>
      match bootEntryContractViolations env entry with
      | [] => logInfo m!"boot-entry contract: `{entry}` boots through `{approvedBootCall}` \
                and installs kernel state no other way"
      | violations => throwError "boot-entry contract: {violations}"
  | entries =>
      throwError "boot-entry contract: {entries.length} declarations export \
        `{bootEntrySymbol}` ({entries}) — the hardware boot entry is one declaration"

end SeLe4n.Testing.BootEntryContract
