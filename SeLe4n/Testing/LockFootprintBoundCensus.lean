-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import Lean.Elab.Command
import SeLe4n
import SeLe4n.Platform.Staged

/-!
# WS-RR RR7.18 — every declared lock footprint has a size bound, at its full arity

`boundedWait_under_2pl`, the `KernelOperation` invariant and the whole WCRT
surface take `S.size ≤ maxLockSetSize` as a premise.  A footprint with no such
theorem has no premise there at all — the reasoning is *silent* about it rather
than conservative, which is strictly worse than a loose bound.

`lockSetTransitions_within_bound` is a hand-written conjunction, and the
register's §6 finding 15 is what a hand-written conjunction cannot do: notice
that it is missing members.  It bounded thirty-one of the tree's footprints, and
nothing said what the tree's footprints were.

## The two questions, and why the second is the one that keeps biting

**Does a bound exist?** — answered by looking for `<name>_size_le`.

**Is it stated at the footprint's full arity?** — answered by comparing types.
This is the question that has failed repeatedly, always the same way: a
footprint gains a trailing `Option` with a `:= none` default, the existing bound
keeps elaborating because the default fills the new argument in silently, and
the shape the live transition actually declares is left unbounded while the
theorem's name still promises a bound.  It happened to `notificationSignal`
(SM9.C.8, the bound-delivery optionals), to `endpointReceive` (PR #873 round 8,
the reply optional and the caps flag), to `endpointSend` and `endpointCall`
(WS-RR RR7.7, the transfer destination), and — found *by this census* — to
`endpointReply`, whose sixth argument `replyId` was defaulted at the bound while
the live `.reply` dispatch resolves it to `some`.

`lockSet_endpointCall_size_le` carries a comment telling the next author not to
use default arguments there.  A comment is a convention; this is the mechanism.

## How it decides

For every constant whose name's last component begins with `lockSet_` and whose
type ends in `LockSet`, the census builds the statement the bound **must** have
— `∀ x₁ … xₙ, (f x₁ … xₙ).size ≤ maxLockSetSize`, over the *definition's own*
telescope — and requires `<name>_size_le` to have exactly that type, decided by
one `isDefEq`.  A bound stated at fewer arguments is a different proposition and
is refused; so is one stated against a different constant.

That is round 21's rule applied here: where the subject is code this project
writes, **require a canonical spelling and refuse the rest**, rather than
analysing whatever an author happened to state.  Building this module is the
check; `scripts/test_tier1_build.sh` builds it.

## What is outside this census, and why that is a decision

The universe is the `lockSet_`-prefixed definitions, and the requirement is an
*unconditional* bound at the full arity — so a footprint **derived from the
state**, whose size no closed theorem bounds, is outside it by construction
rather than by omission.  The one such footprint in the tree is the CSpace
walk's (`Capability.cspaceWalkLockSet`), which reads one key per level of the
walk and therefore grows with the CSpace rather than with the operation's
arguments (PR #892 review round 4).  Giving it a census-visible name would have
registered a footprint the census could only ever refuse.  Its bound is
enforced where a state-derived set can be bounded — at its **declaration**:
`declaredLockSetForCSpaceWalk` answers `none` for a walk whose set exceeds
`maxLockSetSize`, `declaredLockSetForCSpaceWalk_some_size_le` says a declared
set is within the bound, and the bracket falls back on a refused one.  A new
state-derived footprint takes the same shape — a declaration that refuses —
and says so in its docstring, since this census will not find it.
-/

namespace SeLe4n.Testing.LockFootprintBoundCensus

open Lean Elab Command Meta

/-- The suffix a footprint's size bound must carry.  One spelling, so a bound
under any other name is a bound this census cannot find — which is deliberate:
a caller looking for the bound of `lockSet_foo` must be able to find it by
name, and `lockSetTransitions_within_bound` cites bare names too. -/
def boundSuffix : String := "_size_le"

/-- Footprints that legitimately carry no `_size_le`, each with the reason.

Empty, and meant to stay that way: every `LockSet` a transition declares is a
set the 2PL bracket may acquire, so every one of them needs the premise.  The
register exists so that a future exemption is a *decision* someone wrote down
rather than a name that quietly failed to appear. -/
def boundExemptions : List (Name × String) := []

/-- Is this a lock-footprint declaration — a `def` whose type ends in
`LockSet`, named `lockSet_…`?

The name test is on the **last component**, so a footprint is found wherever it
is declared; the type test is what makes it a footprint rather than something
that merely reads like one. -/
def isFootprintDecl (env : Environment) (n : Name) : MetaM Bool := do
  match n with
  | .str _ s =>
    if !s.startsWith "lockSet_" then return false
    if s.endsWith boundSuffix then return false
    match env.find? n with
    | some (.defnInfo info) =>
        forallTelescopeReducing info.type fun _ result => do
          let result ← whnf result
          return result.isConstOf ``SeLe4n.Kernel.Concurrency.LockSet
    | _ => return false
  | _ => return false

/-- The statement `<name>_size_le` is required to have: the footprint's own
telescope, applied to its own binders, bounded by `maxLockSetSize`.

Built from the definition, so it cannot be under-applied: the binders are the
definition's, and a theorem stated at fewer of them is a different type. -/
def requiredBoundType (n : Name) (declType : Expr) : MetaM Expr :=
  forallTelescopeReducing declType fun xs _ => do
    let applied := mkAppN (mkConst n) xs
    let size := mkApp (mkConst ``SeLe4n.Kernel.Concurrency.LockSet.size) applied
    let bound ← mkAppM ``LE.le #[size, mkConst ``SeLe4n.Kernel.Concurrency.maxLockSetSize]
    mkForallFVars xs bound

/-- The verdict for one footprint: `none` when it is bounded correctly, else the
reason it is not. -/
def boundViolation (env : Environment) (n : Name) : MetaM (Option String) := do
  if boundExemptions.any (fun p => p.1 == n) then return none
  let some (.defnInfo info) := env.find? n | return some "not a definition"
  let boundName :=
    match n with
    | .str p s => Name.str p (s ++ boundSuffix)
    | _ => n
  let some boundInfo := env.find? boundName
    | return some s!"has no {boundName} — a footprint with no size bound is a \
         transition the bounded-wait and WCRT reasoning is SILENT about"
  let required ← requiredBoundType n info.type
  if ← isDefEq boundInfo.type required then
    return none
  else
    return some s!"{boundName} exists but does not state the bound at the \
      footprint's full arity — a defaulted trailing argument is filled in \
      silently, so the shape the live transition declares is unbounded while \
      the name still promises a bound"

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mut footprints : Array Name := #[]
  for (n, _) in env.constants.toList do
    if ← isFootprintDecl env n then
      footprints := footprints.push n
  let sortedFootprints := footprints.qsort (fun a b => a.toString < b.toString)
  if sortedFootprints.size == 0 then
    throwError "lock-footprint census: found NO footprints, so it would pass \
      vacuously — the name or type test is wrong"
  let mut violations : Array String := #[]
  for n in sortedFootprints do
    match ← boundViolation env n with
    | some why => violations := violations.push s!"  {n}: {why}"
    | none => pure ()
  if violations.size != 0 then
    throwError "lock-footprint census: {violations.size} of {sortedFootprints.size} \
      declared footprints are not soundly bounded:\n{String.intercalate "\n" violations.toList}"
  logInfo s!"lock-footprint census: {sortedFootprints.size} declared LockSet footprints, \
    every one bounded by maxLockSetSize at its full arity"

end SeLe4n.Testing.LockFootprintBoundCensus
