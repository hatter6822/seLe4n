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

/-- The value of `n`, or `none` for a declaration that has none (an axiom, a
constructor).

`allowOpaque := true`: an `opaque` declaration's body is hidden by default, and
an entry must be *seen* to be refused rather than treated as absent. -/
def declarationValue (env : Environment) (n : Name) : Option Expr :=
  (env.find? n).bind (·.value? (allowOpaque := true))

/-- **PR #889 review round 21: the entry is required to be one program, not
analysed as an arbitrary one.**

Rounds 18 through 21 were four consecutive findings against a hand-written
abstract interpreter this file used to carry — `unconditionalActions`, a walk
that tried to decide *what an arbitrary `BaseIO` term does*: whether the boot
ran on every path (round 18), whether the `Bind` instance sequencing it was
lawful (round 19), whether an `opaque` body hid an installer (round 19),
whether an action before it returned at all (round 20), whether a `let`-bound
head denoted a halt (round 21).  Each fix was correct and the next round found
another form, for the reason round 16 had already written down about regular
expressions: *the set of inputs that defeats a partial analysis is unbounded
while the set it has seen is finite.*  Round 17 moved the **name** questions to
the elaborator and ended that sub-class outright, because a constant has one
definition; it left the **behavioural** question to a new hand-rolled walk, and
the elaborator does not answer "what does this program do".

So the walk is gone, and the contract is the exit round 16 named for exactly
this situation — code this project writes, which does not exist yet: *require a
canonical spelling and refuse the rest.*  The entry's body must **be** the
approved boot applied to a configuration:

    fun dtbPointer => Platform.FFI.bootAndInitialiseRPi5OrHalt (config dtbPointer)

Every question the walk approximated is then either answered exactly or has no
subject.  Does the boot execute?  The entry *is* the boot.  Does anything
diverge before it?  Nothing precedes it.  Is the `Bind` instance lawful?  There
is no bind.  Is a `let`-bound head normalized?  `isDefEq` zeta-reduces, and
beta-reduces, and sees through `mdata`, aliases and notation, because that is
what definitional equality is.  Does some reachable declaration install kernel
state?  Nothing else runs — which makes this contract *stronger* than the walk
it replaces, not weaker: that one permitted arbitrary extra actions provided
none of them wrote kernel state.

The argument is where the strength comes from, and it is type-theoretic rather
than analysed: `PlatformConfig` is **data**.  A term of that type performs no
effects, installs nothing, cannot halt and has no monadic structure, so no
walk over it is needed or possible.  Whatever SM10.1 derives from the DTB
pointer, deriving it cannot bypass the checked boot.

What this deliberately refuses is an entry that needs *effects* to build its
configuration (`do let cfg ← readDtb ptr; boot cfg`).  That is not an oversight:
such a prologue is an arbitrary `BaseIO` program again, and this file has four
rounds of evidence that it cannot be analysed.  If SM10.1 needs one, the
kernel supplies it as a definition — `bootAndInitialiseRPi5FromDtb`, wrapping
the read and the boot — and `approvedBootCall` moves to that wrapper, which is
a one-line change here and a reviewed one there.  Refusing what cannot be
decided is the posture; silently admitting it is what the walk did. -/
def isApprovedBootApplication (value : Expr) : MetaM Bool :=
  Meta.lambdaTelescope value fun _ body => do
    let configType := mkConst ``SeLe4n.Platform.Boot.PlatformConfig
    let config ← Meta.mkFreshExprMVar configType
    Meta.isDefEq body (mkApp (mkConst approvedBootCall) config)


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
  let shaped ← match declarationValue env entry with
    | some value =>
        if ← isApprovedBootApplication value then pure []
        else pure [s!"`{entry}` is not `{approvedBootCall}` applied to a configuration.  The \
                      hardware boot entry must *be* that application — the checked platform \
                      boot with its failure handled, so a refused boot parks the PE instead of \
                      returning to Rust with no kernel state — and nothing else, so no other \
                      path can install kernel state around it.  A prologue that computes the \
                      configuration with effects is refused deliberately: the kernel supplies \
                      such a wrapper as a definition and this contract names it"]
    | none => pure [s!"`{entry}` has no value to check — a declaration without a body cannot \
                       be the boot entry"]
  return typed ++ shaped

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
could be; the elaboration below requires the contract to accept the compliant
ones and refuse the rest.  Each deviation **keeps** the tokens a text scanner
looks for — the boot call, the halt, the `match`, the `.error` arm — and breaks
the relation, which is the mutation this repository's gates are tested by.

Round 21 changed which side several of these fall on, and that is the point of
the change: the walk they were written against admitted any entry whose extra
actions happened not to write kernel state, so a *sequence* around the boot
passed.  Under the contract nothing runs but the boot, so `Sequenced`,
`HaltedFirst`, `AliasHaltedFirst`, `BogusBind`, `OpaqueBypass` and `SideInstall`
are refused for one reason instead of six — which is what it means for a class
to be closed rather than enumerated.  Two accepted witnesses keep the contract
from being merely restrictive: an entry that binds its configuration with a
`let`, and one that reaches the same program through an alias — both are that
application after reduction, and `isDefEq` says so. -/

/-- The configuration SM10.1 derives from the DTB pointer.  A placeholder: the
witnesses need *a* pure `UInt64 → PlatformConfig`, and the real derivation
(`Platform.DeviceTree` against the blob `rust_boot_main` passes) is SM10.1's. -/
private def bootEntryWitnessConfig (_dtbPointer : UInt64) : Platform.Boot.PlatformConfig :=
  { irqTable := [], initialObjects := [] }

/-- An alias of the approved boot, for the acceptance witness below. -/
private def bootEntryWitnessBootAlias : Platform.Boot.PlatformConfig → BaseIO Unit :=
  Platform.FFI.bootAndInitialiseRPi5OrHalt

/-- The shape SM10.1's entry must have, at the type its `extern "C"`
declaration is called at. -/
private def bootEntryWitnessCompliant (dtbPointer : UInt64) : BaseIO Unit :=
  Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer)

/-- The approved call reached through a `do` chain.  **Refused** since round 21,
where the walk accepted it: a sequence is an arbitrary `BaseIO` program in the
action position, and four rounds of findings are the evidence that such a
program cannot be analysed — a lawless `Bind`, an `opaque` body, a halt, a
`let`-bound head each defeated one version of the walk.  The entry performs the
boot and nothing else. -/
private def bootEntryWitnessSequenced (dtbPointer : UInt64) : BaseIO Unit := do
  let _ ← Platform.FFI.getKernelState
  Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer)

/-- The configuration bound by a `let` — round 21's finding, in the position it
was reported at.  **Accepted**: `isDefEq` zeta-reduces, so this *is* the
approved application, and no `letE` arm has to be written to see it. -/
private def bootEntryWitnessLetBoundConfig (dtbPointer : UInt64) : BaseIO Unit :=
  let config := bootEntryWitnessConfig dtbPointer
  Platform.FFI.bootAndInitialiseRPi5OrHalt config

/-- The same program reached through an alias of the approved call.
**Accepted**, and it is what keeps the contract from being a name match: the
alias is a different constant and the same program, which is exactly the
distinction definitional equality makes and a spelling comparison does not. -/
private def bootEntryWitnessAliasedBoot (dtbPointer : UInt64) : BaseIO Unit :=
  bootEntryWitnessBootAlias (bootEntryWitnessConfig dtbPointer)

/-- Keeps the approved call and puts it *inside a branch* (PR #889 review round
18).  Every token a scanner reads is present and no other state writer is
reachable; on the path any real configuration takes, nothing boots. -/
private def bootEntryWitnessConditional (dtbPointer : UInt64) : BaseIO Unit :=
  if dtbPointer == 0 then
    Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer)
  else pure ()

/-- Parks the PE and *then* boots (PR #889 review round 20).  Every token is
present, the `Bind` instance is canonical, and the boot is unreachable. -/
private def bootEntryWitnessHaltedFirst (dtbPointer : UInt64) : BaseIO Unit := do
  Platform.FFI.ffiFatalHaltAll
  Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer)

/-- The same through an *alias* of the primitive, so a name match is not what
decides it. -/
private def bootEntryWitnessAliasHaltedFirst (dtbPointer : UInt64) : BaseIO Unit := do
  Kernel.Concurrency.fatalHaltAll
  Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer)

/-- Round 21's reported case, verbatim: the halt reached through a `let`-bound
name, so the first action's head is a bound variable rather than a constant.
That defeated the walk's non-returning derivation — which is the last such form
this file will have to know about, since the contract does not ask what the
first action is. -/
private def bootEntryWitnessLetBoundHalt (dtbPointer : UInt64) : BaseIO Unit := do
  let halt := Platform.FFI.ffiFatalHaltAll
  halt
  Platform.FFI.bootAndInitialiseRPi5OrHalt (bootEntryWitnessConfig dtbPointer)

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
  -- The contract is not vacuously satisfiable: the approved call must resolve
  -- to a declaration of *this* environment, or every entry would be refused
  -- for the same uninformative reason and the witnesses below would pass by
  -- accident.
  unless (env.find? approvedBootCall).isSome do
    throwError "boot-entry contract: `{approvedBootCall}` is not a declaration of this \
      environment, so the shape the entry is held to does not exist"
  -- The witnesses.
  -- Accepted: the required program, however it is spelled.  Without these the
  -- contract could be refusing everything and read exactly the same.
  for witness in [``bootEntryWitnessCompliant, ``bootEntryWitnessLetBoundConfig,
                  ``bootEntryWitnessAliasedBoot] do
    let violations ← bootEntryContractViolations witness
    unless violations.isEmpty do
      throwError "boot-entry contract: the compliant witness `{witness}` was refused: \
        {violations}"
  -- Refused: every other program.  Each keeps the tokens a scanner reads.
  for witness in [``bootEntryWitnessConditional, ``bootEntryWitnessWrongType,
                  ``bootEntryWitnessBypass, ``bootEntryWitnessSideInstall,
                  ``bootEntryWitnessUnbooted, ``bootEntryWitnessBogusBind,
                  ``bootEntryWitnessOpaqueBypass, ``bootEntryWitnessHaltedFirst,
                  ``bootEntryWitnessAliasHaltedFirst, ``bootEntryWitnessSequenced,
                  ``bootEntryWitnessLetBoundHalt] do
    if (← bootEntryContractViolations witness).isEmpty then
      throwError "boot-entry contract: the deviating witness `{witness}` was accepted"
  -- The contract itself.
  match bootEntryDeclarations env with
  | [] =>
      logInfo m!"boot-entry contract: no declaration exports `{bootEntrySymbol}` yet \
        (SM10.1 writes it); the contract is pinned by its thirteen witnesses"
  | [entry] =>
      match ← bootEntryContractViolations entry with
      | [] => logInfo m!"boot-entry contract: `{entry}` is `{approvedBootCall}` applied \
                to a configuration, and nothing else"
      | violations => throwError "boot-entry contract: {violations}"
  | entries =>
      throwError "boot-entry contract: {entries.length} declarations export \
        `{bootEntrySymbol}` ({entries}) — the hardware boot entry is one declaration"

end SeLe4n.Testing.BootEntryContract
