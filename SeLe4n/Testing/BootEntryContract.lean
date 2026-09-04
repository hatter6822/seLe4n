-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import Lean.Elab.Command
-- Both roots.  `SeLe4n` is the production library — the import closure Lake
-- compiles into `SeLe4n:static`, and therefore the set of modules whose
-- `@[export]` can emit a symbol a kernel image links.  `Platform.Staged` pulls
-- the staged modules in beside it.  PR #889 review round 18: with `Staged`
-- alone, an entry SM10.1 defines in a module imported only by `SeLe4n.lean`
-- would be a symbol in the archive and *absent from this environment*, so the
-- contract would log itself vacuous while the Python link check saw the symbol
-- — the two halves disagreeing in the one direction neither can catch.
import SeLe4n
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

/-- The value of `n`, or `none` for a declaration that has none (an axiom, a
constructor).

`allowOpaque := true` (PR #889 review round 19).  `ConstantInfo.value?` hides
an `opaque` declaration's body by default, so the reachability walk treated one
as a harmless leaf and
`opaque overwrite : SystemState → BaseIO Unit := initialiseKernelState`, called
after the approved boot, replaced the checked state while passing the contract.

What this still cannot see is a body that is not Lean's: an `@[extern]`
`opaque` has a foreign implementation, and its Lean-side value is the
`Inhabited`/`Nonempty` witness the elaborator synthesised.  Such a body cannot
name `kernelStateRef` — an `IO.Ref` no foreign code holds — so the walk is
sound for the property it states; a foreign function that called *back* into an
exported Lean installer would be outside it, and is the readiness-gate and
export-inventory surface's question rather than this one's. -/
def declarationValue (env : Environment) (n : Name) : Option Expr :=
  (env.find? n).bind (·.value? (allowOpaque := true))

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

/-- Is `inst` the `Bind BaseIO` instance, up to definitional equality? -/
def isCanonicalBaseIOBind (inst : Expr) : MetaM Bool := do
  let canonical ← Meta.synthInstance (← Meta.mkAppM ``Bind #[mkConst ``BaseIO])
  Meta.isDefEq inst canonical

/-- The actions `e` performs **unconditionally**, in order.

PR #889 review round 18: `getUsedConstants` says a constant *occurs* in the
elaborated term, which is a presence check — the very substitution this
repository's scanners are held against, one level down from text.
`if config.initialObjects.isEmpty then bootAndInitialiseRPi5OrHalt config else
pure ()` mentions the approved call, reaches no other state writer, and boots
nothing on the path any real configuration takes.

Occurrence becomes execution along the structure that cannot branch: binders,
`let`s, metadata, and a monadic bind, whose two action arguments both run.  A
conditional or a `match` is *not* on that spine — it appears here as one action
whose head is `ite` / `dite` / a matcher, which is not the approved call, so it
satisfies nothing.  An entry may still branch (`do foo; if c then a else b;
boot cfg` is accepted, because the boot is on the spine regardless of `c`);
what it may not do is put the boot itself inside a branch. -/
partial def unconditionalActions (e : Expr) : MetaM (List Expr) := do
  match e with
  | .mdata _ body => unconditionalActions body
  | .lam _ _ body _ => unconditionalActions body
  | .letE _ _ _ body _ => unconditionalActions body
  | .app .. =>
      if e.getAppFn.constName? == some ``Bind.bind then
        let args := e.getAppArgs
        -- `@Bind.bind m inst α β (action) (continuation)`.  The *instance*
        -- decides whether this sequences at all (PR #889 review round 19): a
        -- lawless `Bind` on a type definitionally equal to `BaseIO Unit` can
        -- return `pure ()` while ignoring both arguments, and the entry's
        -- pinned type would not notice.  So the instance must be the one
        -- instance synthesis finds for `Bind BaseIO`; anything else is one
        -- opaque action, which is not the approved call and satisfies nothing.
        if args.size < 2 then return [e]
        else if ← isCanonicalBaseIOBind args[1]! then
          return args[args.size - 2]! :: (← unconditionalActions args[args.size - 1]!)
        else return [e]
      else return [e]
  | _ => return [e]

/-- Is `approvedBootCall` the head of an action the entry performs on every
path?  `unconditionalActions` explains why this is the honest form of the
question. -/
def executesApprovedBootCall (env : Environment) (entry : Name) : MetaM Bool := do
  match declarationValue env entry with
  | some value =>
      return (← unconditionalActions value).any fun action =>
        action.getAppFn.constName? == some approvedBootCall
  | none => return false

/-- The type the exported entry must have.

`rust/sele4n-hal/src/boot.rs` declares `extern "C" { fn lean_kernel_main(dtb_ptr:
u64); }`, and a C symbol carries no type information, so the linker accepts a
Lean declaration of *any* shape under that name and Rust then calls it with an
incompatible ABI — passing the DTB address where the wrapper expects a boxed
`lean_object*`, for instance.  `UInt64 → BaseIO Unit` is the same Lean type the
tree's other `fn lean_x(arg: u64)` seams already carry
(`lean_per_core_timer_tick`, `lean_secondary_kernel_main`), so this pins the
convention rather than inventing one (PR #889 review round 18). -/
def expectedBootEntryType : Expr :=
  .forallE `dtbPointer (mkConst ``UInt64) (mkApp (mkConst ``BaseIO) (mkConst ``Unit)) .default

/-- Why `entry` does not meet the boot-entry contract; `[]` when it does. -/
def bootEntryContractViolations (entry : Name) : MetaM (List String) := do
  let env ← getEnv
  let typed ← match env.find? entry with
    | some info =>
        if ← Meta.isDefEq info.type expectedBootEntryType then pure []
        else pure [s!"`{entry}` has type `{info.type}`, and the hardware boot entry must have \
                      the type its `extern \"C\"` declaration is called at — \
                      `UInt64 → BaseIO Unit`, the DTB pointer `rust_boot_main` passes.  A C \
                      symbol carries no type, so the link succeeds and the ABI does not"]
    | none => pure [s!"`{entry}` is not a declaration of this environment"]
  let missing :=
    if ← executesApprovedBootCall env entry then []
    else [s!"`{entry}` does not perform `{approvedBootCall}` as an unconditional action — the \
             hardware boot entry must boot through the checked platform boot with its failure \
             handled, so a refused boot parks the PE instead of returning to Rust with no \
             kernel state, and it must do so on every path rather than merely mention the call"]
  let bypass :=
    match unapprovedKernelStateWrite env (stateReferenceSet.insert approvedBootCall)
            [entry] {} with
    | some writer =>
        [s!"`{entry}` reaches `{writer}`, which installs kernel state without going through \
            `{approvedBootCall}` — a path around the checked boot leaves the live state \
            without the idle threads, the deployment labeling and the reserved slots it \
            establishes"]
    | none => []
  return typed ++ missing ++ bypass

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
reads exactly like a passing one.  These declarations are what a boot entry
could be; the elaboration below requires the analysis to accept the first and
refuse the others.  Each deviation **keeps** the tokens a text scanner looks
for — the boot call, the halt, the `match`, the `.error` arm — and breaks the
relation, which is the mutation this repository's gates are tested by. -/

/-- The configuration SM10.1 derives from the DTB pointer.  A placeholder: the
witnesses need *a* pure `UInt64 → PlatformConfig`, and the real derivation
(`Platform.DeviceTree` against the blob `rust_boot_main` passes) is SM10.1's. -/
private def bootEntryWitnessConfig (_dtbPointer : UInt64) : Platform.Boot.PlatformConfig :=
  { irqTable := [], initialObjects := [] }

/-- The shape SM10.1's entry must have, at the type its `extern "C"`
declaration is called at. -/
private def bootEntryWitnessCompliant (dtbPointer : UInt64) : BaseIO Unit :=
  Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer)

/-- The approved call reached through a `do` chain — the continuation of a
bind rather than its first action.  Accepted: a sequence has no paths, so the
boot still runs unconditionally.  This witness is what makes the bind recursion
in `unconditionalActions` load-bearing; without it, a recursion that stopped at
the first action would pass every other case here. -/
private def bootEntryWitnessSequenced (dtbPointer : UInt64) : BaseIO Unit := do
  let _ ← Platform.FFI.getKernelState
  Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer)

/-- Keeps the approved call and puts it *inside a branch* (PR #889 review round
18).  Every token a scanner reads is present and no other state writer is
reachable; on the path any real configuration takes, nothing boots. -/
private def bootEntryWitnessConditional (dtbPointer : UInt64) : BaseIO Unit :=
  if dtbPointer == 0 then
    Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer)
  else pure ()

/-! The bogus-monad witness (PR #889 review round 19).  `BootEntryBogusMonad α`
is definitionally `BaseIO Unit`, so an application of `Bind.bind` at *this*
instance has the type the entry is pinned to — and the instance discards both
arguments, so nothing it is handed runs. -/
private def BootEntryBogusMonad (_α : Type) : Type := BaseIO Unit

private instance : Bind BootEntryBogusMonad where
  bind _ _ := (pure () : BaseIO Unit)

/-- Keeps the approved call in a bind's action position, under an instance that
never runs it.  The head is `Bind.bind` and the entry's type is right; only the
*instance* distinguishes this from the sequenced witness. -/
private def bootEntryWitnessBogusBind (dtbPointer : UInt64) : BaseIO Unit :=
  @Bind.bind BootEntryBogusMonad inferInstance PUnit PUnit
    (Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer))
    (fun _ => (pure () : BaseIO Unit))

/-- An `opaque` alias of a kernel-state installer (PR #889 review round 19).
`ConstantInfo.value?` hid its body by default, so the reachability walk read it
as a leaf. -/
private opaque bootEntryWitnessOpaqueInstaller : Model.SystemState → BaseIO Unit :=
  Platform.FFI.initialiseKernelState

/-- Boots through the approved call and then installs state through that
opaque alias. -/
private def bootEntryWitnessOpaqueBypass (dtbPointer : UInt64) : BaseIO Unit := do
  Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer)
  bootEntryWitnessOpaqueInstaller default

/-- Keeps the approved call and takes the *wrong* argument type (PR #889 review
round 18).  A C symbol carries no type, so this links and Rust then calls it
with the DTB address in a boxed-pointer position. -/
private def bootEntryWitnessWrongType (config : Platform.Boot.PlatformConfig) : BaseIO Unit :=
  Platform.FFI.bootAndInitialiseRPi5OrHalt config

/-- Keeps the checked boot, the `match`, the `.error` arm and the halt, and
installs the state itself — so a *later* change to what the checked boot
establishes would not reach the live state. -/
private def bootEntryWitnessBypass (dtbPointer : UInt64) : BaseIO Unit := do
  match ← Platform.FFI.bootAndInitialiseRPi5 (bootEntryWitnessConfig dtbPointer) with
  | .ok st => Platform.FFI.initialiseKernelState st
  | .error _ => Platform.FFI.ffiFatalHaltAll

/-- Keeps the approved call *and* installs state beside it. -/
private def bootEntryWitnessSideInstall (dtbPointer : UInt64) : BaseIO Unit := do
  Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer)
  Platform.FFI.initialiseKernelState default

/-- Installs nothing at all: the image would idle with no kernel. -/
private def bootEntryWitnessUnbooted (_dtbPointer : UInt64) : BaseIO Unit :=
  pure ()

run_cmd Command.liftTermElabM do
  let env ← getEnv
  -- The environment is the production one.  A witness cannot pin this — the
  -- harm appears only once an entry exists in a module `SeLe4n.lean` alone
  -- imports — but the module list can, exactly (PR #889 review round 18).
  unless env.header.moduleNames.contains `SeLe4n do
    throwError "boot-entry contract: the production library root `SeLe4n` is not in this \
      environment, so an entry defined in a module only it imports would read as absent and \
      the contract would pass vacuously while the archive carried the symbol"
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
  for witness in [``bootEntryWitnessCompliant, ``bootEntryWitnessSequenced] do
    let violations ← bootEntryContractViolations witness
    unless violations.isEmpty do
      throwError "boot-entry contract: the compliant witness `{witness}` was refused: \
        {violations}"
  for witness in [``bootEntryWitnessConditional, ``bootEntryWitnessWrongType,
                  ``bootEntryWitnessBypass, ``bootEntryWitnessSideInstall,
                  ``bootEntryWitnessUnbooted, ``bootEntryWitnessBogusBind,
                  ``bootEntryWitnessOpaqueBypass] do
    if (← bootEntryContractViolations witness).isEmpty then
      throwError "boot-entry contract: the deviating witness `{witness}` was accepted"
  -- The contract itself.
  match bootEntryDeclarations env with
  | [] =>
      logInfo m!"boot-entry contract: no declaration exports `{bootEntrySymbol}` yet \
        (SM10.1 writes it); the analysis is pinned by its nine witnesses"
  | [entry] =>
      match ← bootEntryContractViolations entry with
      | [] => logInfo m!"boot-entry contract: `{entry}` boots through `{approvedBootCall}` \
                and installs kernel state no other way"
      | violations => throwError "boot-entry contract: {violations}"
  | entries =>
      throwError "boot-entry contract: {entries.length} declarations export \
        `{bootEntrySymbol}` ({entries}) — the hardware boot entry is one declaration"

end SeLe4n.Testing.BootEntryContract
