/-
seLe4n  - A Lean Microkernel
Copyright (C) 2026  Adam Hall
This program comes with ABSOLUTELY NO WARRANTY.
This is free software, and you are welcome to redistribute it
under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import Lean.Elab.Command
import Lean.Meta.Basic

/-!
# Which declarations carry a body

Four of this tree's Tier 1 censuses derive a **domain** from the environment, and
every one of them has to answer the same question first: *is this constant a
declaration somebody wrote a body for?*  A constant that is one belongs in the
domain, is walked, and owes whatever the census demands; a constant that is not
— a proof, an axiom, a type former, a data constructor, a recursor — belongs to
none of them.

Until `v0.35.114` that question had **five** answers.  `ReplyStackWriteCensus`
got it right (`.defnInfo` *or* `.opaqueInfo`); `KernelTransitionReachabilityCensus`,
`LockFootprintBoundCensus` (twice) and `IpcDethreadingEnvironmentCensus` (twice)
each matched `.defnInfo` alone and wildcarded the rest, so an `opaque`
declaration — which is executable, which the kernel's FFI surface has
seventy-odd of, and whose body `ConstantInfo.value? (allowOpaque := true)`
hands back — was silently outside four derived domains at once.  PR #897's review
reported one of them.

**A domain miss is silent by construction**, which is why this had to become one
answer rather than four patches: the constant is never examined, the pin never
moves, and each census goes on reporting that its whole domain is accounted for.
The right answer was already in the tree and *unreachable* from two of the
askers, which is this project's own rule — when a question has one owner and an
asker that cannot see it, the owner is in the wrong layer.  So the owner is here,
upstream of every census and of the kernel vocabulary they differ in.
-/

namespace SeLe4n.Testing.DeclarationKind

open Lean

/-- `true` when `ci` is a declaration whose body somebody wrote.

**Every `ConstantInfo` constructor is answered explicitly and there is no `_`
case.**  A wildcard here is what produced the defect this module exists to
retire, and it fails in the worst direction available to a *domain*: a
requirement dropped is a check nobody runs.  With the match exhaustive, a ninth
constructor in a future toolchain is a **build error** naming this function
rather than a silent exclusion — the strongest form of *a scanner's default
branch is a decision*.  `scripts/check_module_axioms.py`'s `axiomSweepEdges` had
enumerated all eight, case for case, since it was written; this is that
precedent, applied to the question the censuses ask.

Two of the six exclusions are **necessary rather than incidental**, and reading
them as "obviously not a definition" is how they end up back under a wildcard.
A `.thmInfo` carries a value — its proof — so a census that wanted "has a body"
in the literal sense would admit it; what excludes it is that a proof is not a
program, and it matters because a type test over the *result* still matches one:
`theorem f : step st = st'` elaborates to `@Eq SystemState (step st) st'`, whose
implicit type argument **is** the constant a `SystemState` domain test looks for,
so a theorem *about* a transition would enter the domain *of* transitions.  And
`.ctorInfo` covers `SystemState.mk`, whose result type is `SystemState` itself: a
constructor assembles a record from its fields and performs no transition.

An `.axiomInfo` has no body at all and this project forbids axioms outright
(`AXIOM_COUNT` is an enforced zero); `.quotInfo` names `Quot`'s four primitives,
none of them a project constant; `.inductInfo` is a type former and `.recInfo`
its recursor, both generated. -/
def bodyBearing : ConstantInfo → Bool
  | .defnInfo _   => true
  | .opaqueInfo _ => true
  | .thmInfo _    => false
  | .axiomInfo _  => false
  | .quotInfo _   => false
  | .inductInfo _ => false
  | .ctorInfo _   => false
  | .recInfo _    => false

/-- The same question of a name, `false` for a name the environment does not
know.  A constant that is absent is not a declaration anyone wrote, and
answering `false` keeps the *domain* answer on the side that must be explained
rather than the side that is never looked at. -/
def bodyBearingName (env : Environment) (n : Name) : Bool :=
  (env.find? n).any bodyBearing

/-! ## Witnesses

`bodyBearing` is a total function over a closed inductive, so the eight arms are
checked by the elaborator — what is *not* checked by the elaborator is that the
two `true` arms are the ones a real environment lands in, and a predicate whose
`opaque` arm nothing on the tree exercises is indistinguishable from one that is
wrong.  These three are the smallest environment lookups that decide it: a
`def`, an `opaque` — the arm the four censuses were missing — and a `theorem` as
the control, since a predicate widened to "carries any value" would admit it.

They are deliberately typed over `Nat`: a witness mentioning `SystemState` or
returning a `LockSet` would enter the domain of one of the censuses downstream
and have to be pinned there, which would make this module's witnesses a
maintenance edge in four files instead of a fact about one function. -/

private def witnessDefinition : Nat → Nat := fun n => n

private opaque witnessOpaque : Nat → Nat := fun n => n

private theorem witnessTheorem : (0 : Nat) = 0 := rfl

run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  let expect (n : Name) (want : Bool) (why : String) : Elab.TermElabM Unit := do
    let some ci := env.find? n
      | throwError "declaration-kind witness `{n}` is missing; without it nothing on \
          this tree exercises the arm it stands for"
    unless bodyBearing ci == want do
      throwError "declaration-kind: `bodyBearing` answers {bodyBearing ci} for `{n}` \
        and must answer {want} — {why}"
  expect ``witnessDefinition true
    "a `def` is the arm every census already had"
  expect ``witnessOpaque true
    "an `opaque` is executable and its body is reachable through \
     `value? (allowOpaque := true)`; excluding it is the defect this module retires"
  expect ``witnessTheorem false
    "a proof carries a value and is not a program, so a predicate widened to \
     `carries any value` would admit it"
  logInfo "declaration-kind: `bodyBearing` decides all eight `ConstantInfo` \
    constructors, with the `def`, `opaque` and `theorem` arms witnessed."

end SeLe4n.Testing.DeclarationKind
